#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/mman.h>
#include "sljitLir.h"

#define LABEL_SIZE 1024

char *p, *lp, // current position in source code
     *data;   // data/bss pointer 
     
int64_t ival,     // current token value       
        *sp, *bp,
        *e, *le,  // current position in emitted code
        *id,      // currently parsed identifier
        *sym;     // symbol table

int     tk,       // current token
        ty,       // current expression type
        loc,      // local variable offset
        line,     // current line number
        src;      // print source and assembly flag

int64_t e_no, *e_lo;
struct sljit_jump *e_jump;
struct sljit_compiler *C;

// Tokens and classes (operators in precedence order)
enum { Num = 128, Fun, Sys, Glo, Loc, Id,
       Char, Else, Enum, If, Int, Int64, Return, Sizeof, While,
       Assign, Cond, Lor, Lan, Or, Xor, And, Eq, Ne, Lt, Gt, Le, Ge,
       Shl, Shr, Add, Sub, Mul, Div, Mod, Inc, Dec, Brak };

// Opcodes for VM (retained for code generation logic, but mapped to SLJIT)
enum { LEA, IMM, JMP, JSR, BZ, BNZ, ENT, ADJ, LEV, LI, LC, SI, SC, PSH,
       OR, XOR, AND, EQ, NE, LT, GT, LE, GE, SHL, SHR, ADD, SUB, MUL, DIV, MOD,
       OPEN, READ, CLOS, GETC, PRTF, MALC, FREE, MSET, MCMP, EXIT };

// Types
enum { CHAR, INT, PTR };

// Identifier offsets in symbol table
enum { Tk, Hash, Name, Class, Type, Val, HClass, HType, HVal, Idsz };

static void     SLJIT_FUNC _drop(sljit_sw n) { sp += n; }
static void     SLJIT_FUNC _push(sljit_sw c) { *--sp = c; }
static int64_t  SLJIT_FUNC _pop() {	return *sp++; }
static int64_t *SLJIT_FUNC _sp() { return sp; }

static int64_t SLJIT_FUNC _open()    { return open((char *)sp[1], *sp); }
static int64_t SLJIT_FUNC _read()    { return read(sp[2], (char *)sp[1], *sp); }
static int64_t SLJIT_FUNC _close()   { return close(*sp); }
static int64_t SLJIT_FUNC _malloc()  { return (int64_t)malloc(*sp); }
static int64_t SLJIT_FUNC _memset()  { return (int64_t)memset((char *)sp[2], sp[1], *sp); }
static int64_t SLJIT_FUNC _memcmp()  { return memcmp((char *)sp[2], (char *)sp[1], *sp); }
static int64_t SLJIT_FUNC _getchar() { return getchar(); }
static void    SLJIT_FUNC _free()    { free((void *)*sp); }
static int64_t SLJIT_FUNC _printf(sljit_sw n) { 
  int64_t *t = sp + n; // Retrieve arguments from the stack in reverse order
  return printf((char *)t[-1], t[-2], t[-3], t[-4], t[-5], t[-6]);
}

struct label_st {
	int64_t e_no;
	struct  sljit_label *e_lab;
};

struct jump_st {
	int64_t e_no;
	struct  sljit_jump *e_jump;
};

struct label_st label_arr[LABEL_SIZE];
struct jump_st  jump_arr[LABEL_SIZE];
int labels_sp, jump_sp;

void jump_pop(int64_t *e_no, struct sljit_jump **e_jump) {
	if (jump_sp <= 0)	{ printf("jump_arr empty\n"); exit(-1); }
	jump_sp--;
	*e_no   = jump_arr[jump_sp].e_no;
	*e_jump = jump_arr[jump_sp].e_jump;
}

// Helper functions for emit_sLjit
void jump_push(int64_t operand, struct sljit_jump *e_jump) {
  int64_t e_no = (int64_t*)operand - e_lo;

  if (jump_sp >= LABEL_SIZE) { printf("jump_arr overflow\n"); exit(-1); }
  jump_arr[jump_sp].e_no   = e_no;
  jump_arr[jump_sp].e_jump = e_jump;
  jump_sp++;
}

void emit_binary_op(int64_t operation) {
  sljit_emit_op1(C, SLJIT_MOV, SLJIT_S0, 0, SLJIT_R0, 0);
  sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_pop));
  sljit_emit_op2(C, operation, SLJIT_R0, 0, SLJIT_R0, 0, SLJIT_S0, 0);
}

void emit_compare_op(int64_t flag, int64_t set_flag) {
  sljit_emit_op1(C, SLJIT_MOV, SLJIT_S0, 0, SLJIT_R0, 0);
  sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_pop));
  sljit_emit_op2u(C, SLJIT_SUB | set_flag, SLJIT_R0, 0, SLJIT_S0, 0);
  sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_IMM, 0);
  sljit_emit_op_flags(C, SLJIT_MOV, SLJIT_R0, 0, flag);
}

// Function to emit SLJIT instructions based on VM opcodes
void emit_sLjit(int64_t *pc) {
  int64_t opcode = *pc++;
  int64_t operand = (opcode <= ADJ) ? *pc++ : 0;

  switch (opcode) {
    case LEA:
      if (operand < 0) { // Variable: local - operand
        sljit_get_local_base(C, SLJIT_R0, 0, -1 * operand * sizeof(sljit_sw));
      } else { // Parameter: (bp = [SLJIT_SP]) + operand - 2 
        sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_MEM1(SLJIT_SP), 0);
        sljit_emit_op2(C, SLJIT_ADD, SLJIT_R0, 0, SLJIT_R0, 0, SLJIT_IMM, (operand-2) * sizeof(sljit_sw));
      }
      break;
    case IMM:
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_IMM, operand);
      break;
    case JMP: jump_push(operand, sljit_emit_jump(C, SLJIT_JUMP)); break;
    case JSR: jump_push(operand, sljit_emit_call(C, SLJIT_CALL, SLJIT_ARGS0(W))); break;
    case BZ:  jump_push(operand, sljit_emit_cmp(C, SLJIT_EQUAL, SLJIT_R0, 0, SLJIT_IMM, 0)); break;
    case BNZ: jump_push(operand, sljit_emit_cmp(C, SLJIT_NOT_EQUAL, SLJIT_R0, 0, SLJIT_IMM, 0)); break;
    case ENT:
      sljit_emit_enter(C, 0, SLJIT_ARGS0(W), 2, 1, (operand+1) * sizeof(sljit_sw));
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_sp));
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_MEM1(SLJIT_SP), 0, SLJIT_R0, 0);
      break;
    case ADJ:
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_S0, 0, SLJIT_R0, 0);
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_IMM, operand);
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS1(W, W), SLJIT_IMM, SLJIT_FUNC_ADDR(_drop));
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_S0, 0);
      break;
    case LEV:
      sljit_emit_return(C, SLJIT_MOV, SLJIT_R0, 0);
      break;
    case LI:
    case LC:
      sljit_emit_op1(C, opcode == LI ? SLJIT_MOV : SLJIT_MOV_U8, SLJIT_R0, 0, SLJIT_MEM1(SLJIT_R0), 0);
      break;
    case SI:
    case SC:
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_S0, 0, SLJIT_R0, 0);
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(P), SLJIT_IMM, SLJIT_FUNC_ADDR(_pop));
      sljit_emit_op1(C, opcode == SI ? SLJIT_MOV : SLJIT_MOV_U8, SLJIT_MEM1(SLJIT_R0), 0, SLJIT_S0, 0);
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_S0, 0);
      break;
    case PSH:
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_S0, 0, SLJIT_R0, 0);
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS1(W, W), SLJIT_IMM, SLJIT_FUNC_ADDR(_push));
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_S0, 0);
      break;
    case OR:  emit_binary_op(SLJIT_OR); break;
    case XOR: emit_binary_op(SLJIT_XOR); break;
    case AND: emit_binary_op(SLJIT_AND); break;
    case EQ:  emit_compare_op(SLJIT_EQUAL, SLJIT_SET_Z); break;
    case NE:  emit_compare_op(SLJIT_NOT_EQUAL, SLJIT_SET_Z); break;
    case LT:  emit_compare_op(SLJIT_SIG_LESS, SLJIT_SET_SIG_LESS); break;
    case GT:  emit_compare_op(SLJIT_SIG_GREATER, SLJIT_SET_SIG_GREATER); break;
    case LE:  emit_compare_op(SLJIT_SIG_LESS_EQUAL, SLJIT_SET_SIG_LESS_EQUAL); break;
    case GE:  emit_compare_op(SLJIT_SIG_GREATER_EQUAL, SLJIT_SET_SIG_GREATER_EQUAL); break;
    case SHL: emit_binary_op(SLJIT_SHL); break;
    case SHR: emit_binary_op(SLJIT_LSHR); break;
    case ADD: emit_binary_op(SLJIT_ADD); break;
    case SUB: emit_binary_op(SLJIT_SUB); break;
    case MUL: emit_binary_op(SLJIT_MUL); break;
    case DIV:
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_S0, 0, SLJIT_R0, 0);
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_pop));
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R1, 0, SLJIT_S0, 0);
      sljit_emit_op0(C, SLJIT_DIV_S32);
      break;
    case MOD:
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_S0, 0, SLJIT_R0, 0);
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_pop));
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R1, 0, SLJIT_S0, 0);
      sljit_emit_op0(C, SLJIT_DIVMOD_S32);
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_R1, 0);
      break;
    case OPEN: sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_open)); break;
    case READ: sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_read)); break;
    case CLOS: sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_close)); break;
    case MALC: sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_malloc)); break;
    case FREE: sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_free)); break;
    case MSET: sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_memset)); break;
    case MCMP: sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_memcmp)); break;
    case GETC: sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS0(W), SLJIT_IMM, SLJIT_FUNC_ADDR(_getchar)); break;
    case PRTF:
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_IMM, *(pc+1)); // para = *(pc+1), ADJ para after JSR
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS1(W, W), SLJIT_IMM, SLJIT_FUNC_ADDR(_printf));
      break;    
    case EXIT:
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_S0, 0, SLJIT_R0, 0);
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_IMM, (int64_t)"exit(%lld)\n");
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS1(W, W), SLJIT_IMM, SLJIT_FUNC_ADDR(_push));
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_S0, 0);
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS1(W, W), SLJIT_IMM, SLJIT_FUNC_ADDR(_push));
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_IMM, 2);
      sljit_emit_icall(C, SLJIT_CALL, SLJIT_ARGS1(W, W), SLJIT_IMM, SLJIT_FUNC_ADDR(_printf));
      sljit_emit_op1(C, SLJIT_MOV, SLJIT_R0, 0, SLJIT_S0, 0);
      sljit_emit_return(C, SLJIT_MOV, SLJIT_R0, 0);
      break;
    default:
      printf("Unknown instruction %lld\n", opcode);
      exit(-1);
  }
}

void next() {
  char *pp;
  while ((tk = *p)) {
    ++p;
    if (tk == '\n') {
      if (src) {
        printf("%d: %.*s", line, (int)(p - lp), lp);
        lp = p;
        while (le < e) {
          printf("%lld: ", (int64_t)(le+1));
          printf("%8.4s", &"LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
                           "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
                           "OPEN,READ,CLOS,GETC,PRTF,MALC,FREE,MSET,MCMP,EXIT,"[(*++le) * 5]);
          if (*le <= ADJ) printf(" %lld\n", *++le); else printf("\n");
        }
      }
      ++line;
    } else if (tk == '#') {
      while (*p != 0 && *p != '\n') ++p;
    } else if ((tk >= 'a' && tk <= 'z') || (tk >= 'A' && tk <= 'Z') || tk == '_') {
      pp = p - 1;
      while ((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || (*p >= '0' && *p <= '9') || *p == '_')
        tk = tk * 147 + *p++;
      tk = (tk << 6) + (p - pp);
      id = sym;
      while (id[Tk]) {
        if (tk == id[Hash] && !memcmp((char *)id[Name], pp, p - pp)) { tk = id[Tk]; return; }
        id = id + Idsz;
      }
      id[Name] = (int64_t)pp;
      id[Hash] = tk;
      tk = id[Tk] = Id;
      return;
    } else if (tk >= '0' && tk <= '9') {
      if ((ival = tk - '0')) { while (*p >= '0' && *p <= '9') ival = ival * 10 + *p++ - '0'; }
      else if (*p == 'x' || *p == 'X') {
        while ((tk = *++p) && ((tk >= '0' && tk <= '9') || (tk >= 'a' && tk <= 'f') || (tk >= 'A' && tk <= 'F')))
          ival = ival * 16 + (tk & 15) + (tk >= 'A' ? 9 : 0);
      } else { while (*p >= '0' && *p <= '7') ival = ival * 8 + *p++ - '0'; }
      tk = Num;
      return;
    } else if (tk == '/') {
      if (*p == '/') {
        ++p;
        while (*p != 0 && *p != '\n') ++p;
      } else {
        tk = Div;
        return;
      }
    } else if (tk == '\'' || tk == '"') {
      pp = data;
      while (*p != 0 && *p != tk) {
        if ((ival = *p++) == '\\') {
          if ((ival = *p++) == 'n') ival = '\n';
        }
        if (tk == '"') *data++ = ival;
      }
      ++p;
      if (tk == '"') ival = (int64_t)pp; else tk = Num;
      return;
    } 
    else if (tk == '=') { if (*p == '=') { ++p; tk = Eq;  } else tk = Assign; return; }
    else if (tk == '+') { if (*p == '+') { ++p; tk = Inc; } else tk = Add; return; }
    else if (tk == '-') { if (*p == '-') { ++p; tk = Dec; } else tk = Sub; return; }
    else if (tk == '!') { if (*p == '=') { ++p; tk = Ne; } return; }
    else if (tk == '<') { if (*p == '=') { ++p; tk = Le; } else if (*p == '<') { ++p; tk = Shl; } else tk = Lt; return; }
    else if (tk == '>') { if (*p == '=') { ++p; tk = Ge; } else if (*p == '>') { ++p; tk = Shr; } else tk = Gt; return; }
    else if (tk == '|') { if (*p == '|') { ++p; tk = Lor; } else tk = Or; return; }
    else if (tk == '&') { if (*p == '&') { ++p; tk = Lan; } else tk = And; return; }
    else if (tk == '^') { tk = Xor; return; }
    else if (tk == '%') { tk = Mod; return; }
    else if (tk == '*') { tk = Mul; return; }
    else if (tk == '[') { tk = Brak; return; }
    else if (tk == '?') { tk = Cond; return; }
    else if (tk == '~' || tk == ';' || tk == '{' || tk == '}' || tk == '(' || tk == ')' || tk == ']' || tk == ',' || tk == ':') return;
  }
}

void expr(int lev) {
  int t;
  int64_t *d;
  if (!tk) { printf("%d: unexpected eof in expression\n", line); exit(-1); }
  else if (tk == Num) { *++e = IMM; *++e = ival; next(); ty = INT; }
  else if (tk == '"') {
    *++e = IMM; *++e = ival; next();
    while (tk == '"') next();
    data = (char *)((int64_t)data + sizeof(int64_t) & -sizeof(int64_t)); ty = PTR;
  } else if (tk == Sizeof) {
    next(); if (tk == '(') next(); else { printf("%d: open paren expected in sizeof\n", line); exit(-1); }
    ty = INT; if (tk == Int || tk == Int64) next(); else if (tk == Char) { next(); ty = CHAR; }
    while (tk == Mul) { next(); ty = ty + PTR; }
    if (tk == ')') next(); else { printf("%d: close paren expected in sizeof\n", line); exit(-1); }
    *++e = IMM; *++e = (ty == CHAR) ? sizeof(char) : sizeof(int64_t);
    ty = INT;
  } else if (tk == Id) {
    d = id; next();
    if (tk == '(') {
      next();
      t = 0;
      while (tk != ')') { expr(Assign); *++e = PSH; ++t; if (tk == ',') next(); }
      next();
      if (d[Class] == Sys) *++e = d[Val];
      else if (d[Class] == Fun) { *++e = JSR; *++e = d[Val]; }
      else { printf("%d: bad function call\n", line); exit(-1); }
      if (t) { *++e = ADJ; *++e = t; }
      ty = d[Type];
    } else if (d[Class] == Num) { *++e = IMM; *++e = d[Val]; ty = INT; }
    else {
      if (d[Class] == Loc) { *++e = LEA; *++e = loc - d[Val]; }
      else if (d[Class] == Glo) { *++e = IMM; *++e = d[Val]; }
      else { printf("%d: undefined variable\n", line); exit(-1); }
      *++e = ((ty = d[Type]) == CHAR) ? LC : LI;
    }
  } else if (tk == '(') {
    next();
    if (tk == Int || tk == Int64 || tk == Char) {
      t = (tk == Int || tk == Int64) ? INT : CHAR; next();
      while (tk == Mul) { next(); t = t + PTR; }
      if (tk == ')') next(); else { printf("%d: bad cast\n", line); exit(-1); }
      expr(Inc);
      ty = t;
    } else {
      expr(Assign);
      if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    }
  } else if (tk == Mul) {
    next(); expr(Inc);
    if (ty > INT) ty = ty - PTR; else { printf("%d: bad dereference\n", line); exit(-1); }
    *++e = (ty == CHAR) ? LC : LI;
  } else if (tk == And) {
    next(); expr(Inc);
    if (*e == LC || *e == LI) --e; else { printf("%d: bad address-of\n", line); exit(-1); }
    ty = ty + PTR;
  } else if (tk == '!') { next(); expr(Inc); *++e = PSH; *++e = IMM; *++e = 0; *++e = EQ; ty = INT; }
  else if (tk == '~') { next(); expr(Inc); *++e = PSH; *++e = IMM; *++e = -1; *++e = XOR; ty = INT; }
  else if (tk == Add) { next(); expr(Inc); ty = INT; }
  else if (tk == Sub) {
    next(); *++e = IMM;
    if (tk == Num) { *++e = -ival; next(); } else { *++e = -1; *++e = PSH; expr(Inc); *++e = MUL; }
    ty = INT;
  } else if (tk == Inc || tk == Dec) {
    t = tk; next(); expr(Inc);
    if (*e == LC) { *e = PSH; *++e = LC; }
    else if (*e == LI) { *e = PSH; *++e = LI; }
    else { printf("%d: bad lvalue in pre-increment\n", line); exit(-1); }
    *++e = PSH;
    *++e = IMM; *++e = (ty > PTR) ? sizeof(int64_t) : sizeof(char);
    *++e = (t == Inc) ? ADD : SUB;
    *++e = (ty == CHAR) ? SC : SI;
  } else { printf("%d: bad expression\n", line); exit(-1); }

  while (tk >= lev) {
    t = ty;
    if (tk == Assign) {
      next();
      if (*e == LC || *e == LI) *e = PSH; else { printf("%d: bad lvalue in assignment\n", line); exit(-1); }
      expr(Assign); *++e = ((ty = t) == CHAR) ? SC : SI;
    } else if (tk == Cond) {
      next();
      *++e = BZ; d = ++e;
      expr(Assign);
      if (tk == ':') next(); else { printf("%d: conditional missing colon\n", line); exit(-1); }
      *d = (int64_t)(e + 3); *++e = JMP; d = ++e;
      expr(Cond);
      *d = (int64_t)(e + 1);
    } 
    else if (tk == Lor) { next(); *++e = BNZ; d = ++e; expr(Lan); *d = (int64_t)(e + 1); ty = INT; }
    else if (tk == Lan) { next(); *++e = BZ;  d = ++e; expr(Or);  *d = (int64_t)(e + 1); ty = INT; }
    else if (tk == Or)  { next(); *++e = PSH; expr(Xor); *++e = OR;  ty = INT; }
    else if (tk == Xor) { next(); *++e = PSH; expr(And); *++e = XOR; ty = INT; }
    else if (tk == And) { next(); *++e = PSH; expr(Eq);  *++e = AND; ty = INT; }
    else if (tk == Eq)  { next(); *++e = PSH; expr(Lt);  *++e = EQ;  ty = INT; }
    else if (tk == Ne)  { next(); *++e = PSH; expr(Lt);  *++e = NE;  ty = INT; }
    else if (tk == Lt)  { next(); *++e = PSH; expr(Shl); *++e = LT;  ty = INT; }
    else if (tk == Gt)  { next(); *++e = PSH; expr(Shl); *++e = GT;  ty = INT; }
    else if (tk == Le)  { next(); *++e = PSH; expr(Shl); *++e = LE;  ty = INT; }
    else if (tk == Ge)  { next(); *++e = PSH; expr(Shl); *++e = GE;  ty = INT; }
    else if (tk == Shl) { next(); *++e = PSH; expr(Add); *++e = SHL; ty = INT; }
    else if (tk == Shr) { next(); *++e = PSH; expr(Add); *++e = SHR; ty = INT; }
    else if (tk == Add) {
      next(); *++e = PSH; expr(Mul);
      if ((ty = t) > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int64_t); *++e = MUL; }
      *++e = ADD;
    } else if (tk == Sub) {
      next(); *++e = PSH; expr(Mul);
      if (t > PTR && t == ty) { *++e = SUB; *++e = PSH; *++e = IMM; *++e = sizeof(int64_t); *++e = DIV; ty = INT; }
      else if ((ty = t) > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int64_t); *++e = MUL; *++e = SUB; }
      else *++e = SUB;
    } 
    else if (tk == Mul) { next(); *++e = PSH; expr(Inc); *++e = MUL; ty = INT; }
    else if (tk == Div) { next(); *++e = PSH; expr(Inc); *++e = DIV; ty = INT; }
    else if (tk == Mod) { next(); *++e = PSH; expr(Inc); *++e = MOD; ty = INT; }
    else if (tk == Inc || tk == Dec) {
      if      (*e == LC) { *e = PSH; *++e = LC; }
      else if (*e == LI) { *e = PSH; *++e = LI; }
      else { printf("%d: bad lvalue in post-increment\n", line); exit(-1); }
      *++e = PSH; *++e = IMM; *++e = (ty > PTR) ? sizeof(int64_t) : sizeof(char);
      *++e = (tk == Inc) ? ADD : SUB;
      *++e = (ty == CHAR) ? SC : SI;
      *++e = PSH; *++e = IMM; *++e = (ty > PTR) ? sizeof(int64_t) : sizeof(char);
      *++e = (tk == Inc) ? SUB : ADD;
      next();
    } else if (tk == Brak) {
      next(); *++e = PSH; expr(Assign);
      if (tk == ']') next(); else { printf("%d: close bracket expected\n", line); exit(-1); }
      if (t > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int64_t); *++e = MUL; }
      else if (t < PTR) { printf("%d: pointer type expected\n", line); exit(-1); }
      *++e = ADD;
      *++e = ((ty = t - PTR) == CHAR) ? LC : LI;
    } else { printf("%d: compiler error tk=%d\n", line, tk); exit(-1); }
  }
}

void stmt() {
  int64_t *a, *b;
  if (tk == If) {
    next();
    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign);
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    *++e = BZ; b = ++e;
    stmt();
    if (tk == Else) {
      *b = (int64_t)(e + 3); *++e = JMP; b = ++e;
      next();
      stmt();
    }
    *b = (int64_t)(e + 1);
  } else if (tk == While) {
    next();
    a = e + 1;
    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign);
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    *++e = BZ; b = ++e;
    stmt();
    *++e = JMP; *++e = (int64_t)a;
    *b = (int64_t)(e + 1);
  } else if (tk == Return) {
    next();
    if (tk != ';') expr(Assign);
    *++e = LEV;
    if (tk == ';') next(); else { printf("%d: semicolon expected\n", line); exit(-1); }
  } else if (tk == '{') {
    next();
    while (tk != '}') stmt();
    next();
  } else if (tk == ';') {
    next();
  } else {
    expr(Assign);
    if (tk == ';') next(); else { printf("%d: semicolon expected\n", line); exit(-1); }
  }
}

int main(int argc, char **argv) {
  int64_t fd, bt, ty;
  int64_t *idmain, *pc;
  int i, poolsz;

  --argc; ++argv;
  if (argc > 0 && **argv == '-' && (*argv)[1] == 's') { src = 1; --argc; ++argv; }
  if (argc < 1) { printf("usage: c4 [-s] [-d] file ...\n"); return -1; }

  if ((fd = open(*argv, 0)) < 0) { printf("could not open(%s)\n", *argv); return -1; }

  poolsz = 256 * 1024;
  if (!(sym  = malloc(poolsz))) { printf("could not malloc(%d) symbol area\n", poolsz); return -1; }
  if (!(e_lo = le = e = malloc(poolsz))) { printf("could not malloc(%d) text area\n", poolsz); return -1; }
  if (!(data = malloc(poolsz))) { printf("could not malloc(%d) data area\n", poolsz); return -1; }
  if (!(sp   = malloc(poolsz))) { printf("could not malloc(%d) stack area\n", poolsz); return -1; }
  
  memset(sym,  0, poolsz);
  memset(e,    0, poolsz);
  memset(data, 0, poolsz);

  p = "char else enum if int int64_t return sizeof while "
      "open read close getchar printf malloc free memset memcmp exit void main";
  i = Char; while (i <= While) { next(); id[Tk] = i++; }
  i = OPEN; while (i <= EXIT)  { next(); id[Class] = Sys; id[Type] = INT; id[Val] = i++; }
  next(); id[Tk] = Char;
  next(); idmain = id;

  if (!(lp = p = malloc(poolsz))) { printf("could not malloc(%d) source area\n", poolsz); return -1; }
  if ((i = read(fd, p, poolsz - 1)) <= 0) { printf("read() returned %d\n", i); return -1; }
  p[i] = 0;
  close(fd);

  line = 1;
  next();
  while (tk) {
    bt = INT;
    if (tk == Int || tk == Int64) next();
    else if (tk == Char) { next(); bt = CHAR; }
    else if (tk == Enum) {
      next();
      if (tk != '{') next();
      if (tk == '{') {
        next();
        i = 0;
        while (tk != '}') {
          if (tk != Id) { printf("%d: bad enum identifier %d\n", line, tk); return -1; }
          next();
          if (tk == Assign) {
            next();
            if (tk != Num) { printf("%d: bad enum initializer\n", line); return -1; }
            i = ival;
            next();
          }
          id[Class] = Num; id[Type] = INT; id[Val] = i++;
          if (tk == ',') next();
        }
        next();
      }
    }
    while (tk != ';' && tk != '}') {
      ty = bt;
      while (tk == Mul) { next(); ty = ty + PTR; }
      if (tk != Id)  { printf("%d: bad global declaration\n", line); return -1; }
      if (id[Class]) { printf("%d: duplicate global definition\n", line); return -1; }
      next();
      id[Type] = ty;
      if (tk == '(') {
        id[Class] = Fun;
        id[Val] = (int64_t)(e + 1);
        next(); i = 0;
        while (tk != ')') {
          ty = INT;
          if (tk == Int || tk == Int64) next();
          else if (tk == Char) { next(); ty = CHAR; }
          while (tk == Mul) { next(); ty = ty + PTR; }
          if (tk != Id) { printf("%d: bad parameter declaration\n", line); return -1; }
          if (id[Class] == Loc) { printf("%d: duplicate parameter definition\n", line); return -1; }
          id[HClass] = id[Class]; id[Class] = Loc;
          id[HType]  = id[Type];  id[Type]  = ty;
          id[HVal]   = id[Val];   id[Val]   = i++;
          next();
          if (tk == ',') next();
        }
        next();
        if (tk != '{') { printf("%d: bad function definition\n", line); return -1; }
        loc = ++i;
        next();
        while (tk == Int || tk == Int64 || tk == Char) {
          bt = (tk == Int || tk == Int64) ? INT : CHAR;
          next();
          while (tk != ';') {
            ty = bt;
            while (tk == Mul) { next(); ty = ty + PTR; }
            if (tk != Id) { printf("%d: bad local declaration\n", line); return -1; }
            if (id[Class] == Loc) { printf("%d: duplicate local definition\n", line); return -1; }
            id[HClass] = id[Class]; id[Class] = Loc;
            id[HType]  = id[Type];  id[Type]  = ty;
            id[HVal]   = id[Val];   id[Val]   = ++i;
            next();
            if (tk == ',') next();
          }
          next();
        }
        *++e = ENT; *++e = i - loc;
        while (tk != '}') stmt();
        *++e = LEV;
        id = sym;
        while (id[Tk]) {
          if (id[Class] == Loc) {
            id[Class] = id[HClass];
            id[Type]  = id[HType];
            id[Val]   = id[HVal];
          }
          id = id + Idsz;
        }
      } else {
        id[Class] = Glo;
        id[Val] = (int64_t)data;
        data = data + sizeof(int64_t);
      }
      if (tk == ',') next();
    }
    next();
  }

  if (!(pc = (int64_t *)idmain[Val])) { printf("main() not defined\n"); return -1; }
  if (src) return 0;

  sp = (int64_t *)((int64_t)sp + poolsz);
 
  *--sp = argc;
  *--sp = (int64_t)argv;

  C = sljit_create_compiler(NULL);
  if (!C) { printf("Could not create SLJIT compiler\n"); return -1; }

  sljit_emit_enter(C, 0, SLJIT_ARGS0(W), 1, 0, 0);
  e_jump = sljit_emit_call(C, SLJIT_CALL, SLJIT_ARGS0(W));
  sljit_emit_return(C, SLJIT_MOV, SLJIT_R0, 0);

  jump_push((int64_t)pc, e_jump);
  label_arr[labels_sp++].e_no = pc - e_lo;

  int64_t addr;
  int64_t found;

  pc = e_lo+1;
  while (pc <= e) {
    if (*pc == JMP || *pc == JSR || *pc == BZ || *pc == BNZ) {
      addr = (int64_t *)pc[1] - e_lo;
      found = 0;
      for (int64_t i = 0; i < labels_sp; i++) {
        if (addr == label_arr[i].e_no) {
          found = 1;
          break;
        }
      }
      if (!found) {
        label_arr[labels_sp++].e_no = addr;
      }
    }
    if (*pc++ <= ADJ) pc++;
  }

  pc = e_lo+1;
  while (pc <= e) {
    for (int64_t i = 0; i < labels_sp; i++) {
      if (pc - e_lo == label_arr[i].e_no) {
        label_arr[i].e_lab = sljit_emit_label(C);
        break;
      }
    }
    emit_sLjit(pc);
    if (*pc++ <= ADJ) pc++;
  }

  while (jump_sp > 0) {
    jump_pop(&e_no, &e_jump);
    for (int64_t i = 0; i < labels_sp; i++) {
      if (e_no == label_arr[i].e_no) {
        sljit_set_label(e_jump, label_arr[i].e_lab);
        break;
      }
    }
  }

  void *code = sljit_generate_code(C, 0, NULL);

  if (!code) {
    printf("Could not generate JIT code\n");
    sljit_free_compiler(C);
    return -1;
  }

  typedef int64_t (*func_t)();
  func_t func = (func_t)code;
  sljit_sw result = func();

  sljit_free_compiler(C);
  sljit_free_code(code, NULL);
  return result;
}

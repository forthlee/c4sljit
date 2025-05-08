// Brainfuck in C
// Slightly altered to work in C4
// Original code borrowed from:
//    http://phimuemue.com/posts/2011-08-04-intermezzo-a-brainf-interpreter.html
//    http://www.github.com/phimuemue

// Usage:
//   $ python c4py.py examples/brainf.c examples/prime.bf
//   Primes up to: 10

#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <unistd.h>
#include <fcntl.h>

int main(int a, char**s){
	int *b, *z, p;
	char *c, v, w;
	int fd, i, poolsz;

	if(a < 2)
		return printf("Usage: %s file.bf\n", s[0]);

	p = 30000;
	if(!(b = z = malloc(p))) return printf("Failed to allocate %d bytes\n", p);
	
	if ((fd = open(s[1], 0)) < 0) { printf("could not open(%s)\n", s[1]); return -1; }
	
	poolsz = 256*1024;
	if (!(c = malloc(poolsz))) { printf("could not malloc(%lld) source area\n", poolsz); return -1; }
	if ((i = read(fd, c, poolsz-1)) <= 0) { printf("read() returned %lld\n", i); return -1; }
	c[i] = 0;
	close(fd);
    
    while(*c) {
		if     (*c == '>') ++z;
		else if(*c == '<') --z;
		else if(*c == '+') ++*z;
		else if(*c == '-') --*z;
		else if(*c == '.') printf("%c", *z);
		else if(*c == ',') *z = getchar();            
		else if(*c == '[') {
			if(!*z) { // 值為0，往前移至配對的']'位址
				p = 1;                
				while(p) { // 往前找配對的']'位址
					c++; 
					if(*c == '[') p++;
					if(*c == ']') p--;
				}
			}
		}
		else if(*c == ']') {            
			p = 1;
			while(p) { // 往後移至配對的'['位址 
				c--;             
				if(*c == '[') p--;
				if(*c == ']') p++;
			}
			c--;
		}
        c++;
    }

    free(b);
    return 0;
}

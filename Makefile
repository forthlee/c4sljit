c4sljit: c4sljit.c
	gcc -DSLJIT_CONFIG_AUTO=1 -I./sljit_src ./sljit_src/sljitLir.c c4sljit.c -o c4sljit

clean:
	rm c4sljit

test: minic.exe
	./minic.exe --debug test.c

minic.exe:
	dune build minic.exe

clean:
	dune clean

.PHONY: clean minic.exe



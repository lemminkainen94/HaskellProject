all:
	happy -gca ParGrammar.y
	alex -g LexGrammar.x
	ghc --make TestGrammar.hs -o TestGrammar
	ghc --make Main.hs

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi Main Main.dyn* TypeChecker.dyn* Interpreter.dyn*
	


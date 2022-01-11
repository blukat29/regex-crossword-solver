clean:
	rm -rf __pycache__ *.pyc parser.out parsetab.py
	cd crossword && rm -rf __pycache__ *.pyc parser.out parsetab.py
	cd crossword/tests && rm -rf __pycache__ *.pyc parser.out parsetab.py

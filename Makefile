.PHONY = all clean doc

all: doc
	pack build idris-http-headers.ipkg

clean:
	pack clean idris-http-headers.ipkg
	@rm -rf build

doc:
	idris2 --mkdoc idris-http-headers.ipkg

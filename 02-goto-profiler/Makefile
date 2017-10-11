JARPATH := src:.:input/classes:bin:libs/jasmin-2.5.0.jar:libs/polyglot.jar:libs/soot-2.5.1.jar
SOOTPATH := .:input/classes:/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/rt.jar
FILE := tst

all: build run

build:
	javac -cp $(JARPATH) ./src/Goto.java -d bin

class:
	clear
	java -cp $(JARPATH) profiler.Goto -cp $(SOOTPATH) -src-prec class -p jb use-original-names -f c -process-dir input/classes

S:
		clear
		java -cp $(JARPATH) profiler.Goto -cp $(SOOTPATH) -src-prec class -p jb use-original-names $(OUT) $(FILE)

clean:
	@rm -r bin sootOutput 2>/dev/null || true
	@mkdir -p bin sootOutput

package profiler;

import java.io.*;
import java.util.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.Jimple;
import soot.util.*;
import soot.util.Chain;

public class GotoCounter {
    public static  void main(String[] args) {
        // check number of arguments ?
        GotoTransformer prof = GotoTransformer.v();

        // aparentemente é utilizado para transformacoes em geral + jimple
        PackManager.v().getPack("jtp").add(new Transform("jtp.gotoCounter",
          prof));

        // // aparentemente utilizado apenas para shimple
        // PackManager.v().getPack("stp").add(new Transform("stp.gotoCounter",
        //     prof));

	      Scene.v().addBasicClass("java.io.PrintStream",SootClass.SIGNATURES);
        Scene.v().addBasicClass("java.lang.System",SootClass.SIGNATURES);
        soot.Main.main(args);
    }
}

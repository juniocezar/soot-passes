package profiler;

import java.io.*;
import java.util.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StringConstant;
import soot.util.*;
import soot.util.Chain;

public class GotoTransformer extends BodyTransformer {
    // Uma abordagem comum no soot é declarar o construtor como privado e ter
    // um metodo estático e publico .v responsável pela instanciação do objeto
    private  GotoTransformer() {}
    public static  GotoTransformer v() { return new GotoTransformer(); }

    private boolean gotoCounterAdded = false;
    private SootClass javaIoPrintStream;
    private SootClass javaStringBuilder;

    protected  void internalTransform(Body body, String phaseName, Map options) {
        SootClass sClass = body.getMethod().getDeclaringClass();
        SootField gotoCounter = null;
        boolean addedLocals = false;
        Local tmpRef = null, tmpLong = null, tmpBuilder1 = null;
        Local tmpBuilder2 = null, tmpBuilder3 = null, tmpBuilder4 = null;
        Local tmpString = null;
        Chain units = body.getUnits();

        // adicionando contador como atributo da classe. Esta sincronizado
        // pois o código pode (deve?) ser executado paralelamente. Queremos
        // evitar a criacao de dois atributos com mesmo nome na classe
        synchronized (this) {
          // so inserimos o contador se encontrarmos a main, pois saberemos
          // que a classe tem um ponto de entrada para retornar os dados
          // gerados
            if (!Scene.v().getMainClass().
                    declaresMethod("void main(java.lang.String[])"))
                throw new RuntimeException("couldn't find main() in java file");

            if (gotoCounterAdded)
                gotoCounter = Scene.v().getMainClass().getFieldByName("gotoCount");
            else {
                // Add gotoCounter field
                gotoCounter = new SootField("gotoCount", LongType.v(),
                                                Modifier.STATIC);
                Scene.v().getMainClass().addField(gotoCounter);

                javaIoPrintStream = Scene.v().getSootClass("java.io.PrintStream");
                javaStringBuilder = Scene.v().getSootClass("java.lang.StringBuilder");

                gotoCounterAdded = true;
            }
          }


        // Inserindo codigo para contar novo goto encontrado

            boolean isMainMethod = body.getMethod().getSubSignature().equals("void main(java.lang.String[])");

            // variavel tmp local ao methodo que recebera uma referencia para o
            // o contador global posteriormente
            Local tmpLocal = Jimple.v().newLocal("tmp", LongType.v());
            // adicionando a definicao dessa variavel com tipo Long, na lista de
            // definicoes do metodo
            body.getLocals().add(tmpLocal);

            // pegamos o snapshotIterator em vez do iterator normal, porque iremos
            // alterar a nossa Chain units enquanto iteramos sobre ela, com isso
            // queremos evitar problemas de concorrencia com leituras e
            // modificacoes da nossa chain de units
            // http://www.sable.mcgill.ca/~plam/doc/soot/util/Chain.html#snapshotIterator()
            Iterator stmtIt = units.snapshotIterator();
            Stmt special = null;

            while(stmtIt.hasNext()) {
                // pegando o primeiro statement do corpo do methodo
                Stmt s = (Stmt) stmtIt.next();

                // caso seja um goto, iremos inserir um incrementador no codigo
                if(s instanceof GotoStmt) {
                    // #1 inserir tmp = gotoCount; (assign)
                    // #2 inserir tmp = tmp + 1;   (sum)
                    // #3 inserir gotoCount = tmp; (update)

                    AssignStmt assign = Jimple.v().newAssignStmt(tmpLocal,
                                 Jimple.v().newStaticFieldRef(gotoCounter.makeRef()));
                    AssignStmt sum = Jimple.v().newAssignStmt(tmpLocal,
                                 Jimple.v().newAddExpr(tmpLocal, LongConstant.v(1L)));
                    AssignStmt update = Jimple.v().newAssignStmt(
                                 Jimple.v().newStaticFieldRef(gotoCounter.makeRef()),
                                 tmpLocal);

                    // inserimos o incrementador antes do goto encontrado
                    units.insertBefore(assign, s);
                    units.insertBefore(sum, s);
                    units.insertBefore(update, s);

                } else if (s instanceof InvokeStmt) {
                    // verificar se podemos ter a chamada da funcao exit
                    // pois devemos imprimir o valor de gotoCounter antes
                    // que o programa encerre sua execucao
                    InvokeExpr iexpr = (InvokeExpr) ((InvokeStmt)s).getInvokeExpr();

                    // especial add news antes na init
                    if (iexpr instanceof SpecialInvokeExpr) {
                        SootMethod target = ((SpecialInvokeExpr)iexpr).getMethod();
                        if (target.getSignature().equals("<java.lang.StringBuilder: void <init>()>")) {
                            special = s;
                        }
                    }
                    else if (iexpr instanceof StaticInvokeExpr) {
                        SootMethod target = ((StaticInvokeExpr)iexpr).getMethod();

                        if (target.getSignature().equals("<java.lang.System: void exit(int)>")) {
                            if (!addedLocals) {
                                tmpRef = Jimple.v().newLocal("$tmpRef", RefType.v("java.io.PrintStream"));
                                body.getLocals().add(tmpRef);

                                tmpLong = Jimple.v().newLocal("$tmpLong", LongType.v());
                                body.getLocals().add(tmpLong);

                                tmpString = Jimple.v().newLocal("$tmpString", RefType.v("java.lang.String"));
                                body.getLocals().add(tmpString);

                                // tmpBuild1 = new java.lang.StringBuilder;
                                tmpBuilder1 = Jimple.v().newLocal("$tmpBuild1", RefType.v("java.lang.StringBuilder"));
                                body.getLocals().add(tmpBuilder1);

                                tmpBuilder2 = Jimple.v().newLocal("$tmpBuild2", RefType.v("java.lang.StringBuilder"));
                                body.getLocals().add(tmpBuilder2);

                                tmpBuilder3 = Jimple.v().newLocal("$tmpBuild3", RefType.v("java.lang.StringBuilder"));
                                body.getLocals().add(tmpBuilder3);

                                tmpBuilder4 = Jimple.v().newLocal("$tmpBuild4", RefType.v("java.lang.StringBuilder"));
                                body.getLocals().add(tmpBuilder4);

                                AssignStmt t1 = Jimple.v().newAssignStmt(tmpBuilder1,
                                    Jimple.v().newNewExpr(RefType.v("java.lang.StringBuilder")));
                                units.insertBefore(t1, s);

                                SpecialInvokeExpr construtor = Jimple.v().newSpecialInvokeExpr(tmpBuilder1,
                                        javaStringBuilder.getMethod("void <init>()").makeRef());
                                units.insertBefore(Jimple.v().newInvokeStmt(construtor), s);


                                addedLocals = true;
                            }

                            // inserir "tmpRef = java.lang.System.out;"
                            AssignStmt refSystemOut = Jimple.v().newAssignStmt(
                                          tmpRef, Jimple.v().newStaticFieldRef(
                                          Scene.v().getField("<java.lang.System: java.io.PrintStream out>").makeRef()));

                            // inserir "tmpLong = gotoCounter;"
                            AssignStmt localCopy = Jimple.v().newAssignStmt(tmpLong,
                                          Jimple.v().newStaticFieldRef(gotoCounter.makeRef()));

                            // inserir "tmpRef.println(tmpLong);"
                            // SootMethod toCall = javaIoPrintStream.getMethod("void println(long)");
                            // InvokeStmt inv = Jimple.v().newInvokeStmt(
                            //               Jimple.v().newVirtualInvokeExpr(tmpRef, toCall.makeRef(), tmpLong));

                            // inserir str = string("gotos found")                    ;
                            SootMethod appendtoCall = javaStringBuilder.getMethod("java.lang.StringBuilder append(java.lang.String)");
                            SootMethod appendtoCallLong = javaStringBuilder.getMethod("java.lang.StringBuilder append(long)");
                            SootMethod toString = javaStringBuilder.getMethod("java.lang.String toString()");
                            // virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Gotos Found: ")
                            InvokeExpr builderInv1 =
                              Jimple.v().newVirtualInvokeExpr(tmpBuilder1, appendtoCall.makeRef(), StringConstant.v("Gotos found: "));
                            // $r2 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Valor: ");
                            AssignStmt s1 = Jimple.v().newAssignStmt(tmpBuilder2, builderInv1);
                            // virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(long)>(gotoCounter);
                            InvokeExpr builderInv2 =
                              Jimple.v().newVirtualInvokeExpr(tmpBuilder2, appendtoCallLong.makeRef(), tmpLong);
                            // $r3 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(long)>(gotoCounter);
                            AssignStmt s2 = Jimple.v().newAssignStmt(tmpBuilder3, builderInv2);

                            // add string srt = stringbuild.toString();
                            //tmpString
                            InvokeExpr genString = Jimple.v().newVirtualInvokeExpr(tmpBuilder3, toString.makeRef());
                            AssignStmt s3 = Jimple.v().newAssignStmt(tmpString, genString);

                            SootMethod toCall = javaIoPrintStream.getMethod("void println(java.lang.String)");
                            InvokeStmt inv = Jimple.v().newInvokeStmt(
                                          Jimple.v().newVirtualInvokeExpr(tmpRef, toCall.makeRef(), tmpString));



                            units.insertBefore(refSystemOut, s);
                            units.insertBefore(localCopy, s);
                            units.insertBefore(s1, s);
                            units.insertBefore(s2, s);
                            units.insertBefore(s3, s);
                            units.insertBefore(inv, s);
                        }
                    }
                }
                else if (isMainMethod && (s instanceof ReturnStmt || s instanceof ReturnVoidStmt)) {
                    // verificar se termos um return na main, pois devemos imprimir
                    // o valor de gotoCounter antes de encerrar a execucao da aplicacao
                    if (!addedLocals) {
                        tmpRef = Jimple.v().newLocal("$tmpRef", RefType.v("java.io.PrintStream"));
                        body.getLocals().add(tmpRef);

                        tmpLong = Jimple.v().newLocal("$tmpLong", LongType.v());
                        body.getLocals().add(tmpLong);

                        tmpString = Jimple.v().newLocal("$tmpString", RefType.v("java.lang.String"));
                        body.getLocals().add(tmpString);

                        // tmpBuild1 = new java.lang.StringBuilder;
                        tmpBuilder1 = Jimple.v().newLocal("$tmpBuild1", RefType.v("java.lang.StringBuilder"));
                        body.getLocals().add(tmpBuilder1);

                        tmpBuilder2 = Jimple.v().newLocal("$tmpBuild2", RefType.v("java.lang.StringBuilder"));
                        body.getLocals().add(tmpBuilder2);

                        tmpBuilder3 = Jimple.v().newLocal("$tmpBuild3", RefType.v("java.lang.StringBuilder"));
                        body.getLocals().add(tmpBuilder3);

                        tmpBuilder4 = Jimple.v().newLocal("$tmpBuild4", RefType.v("java.lang.StringBuilder"));
                        body.getLocals().add(tmpBuilder4);

                        AssignStmt t1 = Jimple.v().newAssignStmt(tmpBuilder1,
                            Jimple.v().newNewExpr(RefType.v("java.lang.StringBuilder")));
                        units.insertBefore(t1, s);

                        SpecialInvokeExpr construtor = Jimple.v().newSpecialInvokeExpr(tmpBuilder1,
                                javaStringBuilder.getMethod("void <init>()").makeRef());
                        units.insertBefore(Jimple.v().newInvokeStmt(construtor), s);


                        addedLocals = true;
                    }
                    // inserir "tmpRef = java.lang.System.out;"
                    AssignStmt refSystemOut = Jimple.v().newAssignStmt(
                                  tmpRef, Jimple.v().newStaticFieldRef(
                                  Scene.v().getField("<java.lang.System: java.io.PrintStream out>").makeRef()));

                    // inserir "tmpLong = gotoCounter;"
                    AssignStmt localCopy = Jimple.v().newAssignStmt(tmpLong,
                                  Jimple.v().newStaticFieldRef(gotoCounter.makeRef()));

                    // inserir "tmpRef.println(tmpLong);"
                    // SootMethod toCall = javaIoPrintStream.getMethod("void println(long)");
                    // InvokeStmt inv = Jimple.v().newInvokeStmt(
                    //               Jimple.v().newVirtualInvokeExpr(tmpRef, toCall.makeRef(), tmpLong));

                    // inserir str = string("gotos found")                    ;
                    SootMethod appendtoCall = javaStringBuilder.getMethod("java.lang.StringBuilder append(java.lang.String)");
                    SootMethod appendtoCallLong = javaStringBuilder.getMethod("java.lang.StringBuilder append(long)");
                    SootMethod toString = javaStringBuilder.getMethod("java.lang.String toString()");
                    // virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Gotos Found: ")
                    InvokeExpr builderInv1 =
                      Jimple.v().newVirtualInvokeExpr(tmpBuilder1, appendtoCall.makeRef(), StringConstant.v("Gotos found: "));
                    // $r2 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Valor: ");
                    AssignStmt s1 = Jimple.v().newAssignStmt(tmpBuilder2, builderInv1);
                    // virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(long)>(gotoCounter);
                    InvokeExpr builderInv2 =
                      Jimple.v().newVirtualInvokeExpr(tmpBuilder2, appendtoCallLong.makeRef(), tmpLong);
                    // $r3 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(long)>(gotoCounter);
                    AssignStmt s2 = Jimple.v().newAssignStmt(tmpBuilder3, builderInv2);

                    // add string srt = stringbuild.toString();
                    //tmpString
                    InvokeExpr genString = Jimple.v().newVirtualInvokeExpr(tmpBuilder3, toString.makeRef());
                    AssignStmt s3 = Jimple.v().newAssignStmt(tmpString, genString);

                    SootMethod toCall = javaIoPrintStream.getMethod("void println(java.lang.String)");
                    InvokeStmt inv = Jimple.v().newInvokeStmt(
                                  Jimple.v().newVirtualInvokeExpr(tmpRef, toCall.makeRef(), tmpString));



                    units.insertBefore(refSystemOut, s);
                    units.insertBefore(localCopy, s);
                    units.insertBefore(s1, s);
                    units.insertBefore(s2, s);
                    units.insertBefore(s3, s);
                    units.insertBefore(inv, s);

                }
            }

    }
}

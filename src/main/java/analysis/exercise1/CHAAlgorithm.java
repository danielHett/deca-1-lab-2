package analysis.exercise1;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import java.util.*;
import java.util.stream.Collectors;

import javax.annotation.Nonnull;

import sootup.java.core.JavaSootClass;
import sootup.java.core.JavaSootMethod;
import sootup.java.core.types.JavaClassType;
import sootup.java.core.views.JavaView;
import sootup.core.signatures.MethodSignature;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.JInvokeStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.typehierarchy.TypeHierarchy;
import sootup.core.types.ClassType;

public class CHAAlgorithm extends CallGraphAlgorithm {

  @Nonnull
  @Override
  protected String getAlgorithm() {
    return "CHA";
  }

  @Override
  protected void populateCallGraph(@Nonnull JavaView view, @Nonnull CallGraph cg) {
    // This should get us the method signatures for all entry points. This is our
    // starting queue.
    Queue<MethodSignature> msq = getEntryPoints(view).collect(Collectors.toCollection(LinkedList::new));

    // Stop when there aren't any nodes left.
    while (msq.peek() != null) {
      MethodSignature m1 = msq.poll();

      // Add the popped node to the graph if it hasn't been already.
      if (!cg.hasNode(m1)) {
        cg.addNode(m1);
      }

      // This *should* find every method signature that m1 (a method) *could* call out
      // to in it's body. So, its accounting
      // for polymorphic call sites.
      for (MethodSignature m2 : findSignaturesInBody(m1)) {
        // Was it in the graph already? Then add it to both the graph and the queue.
        if (!cg.hasNode(m2)) {
          cg.addNode(m2);
          msq.add(m2);
        }

        // Add the edge, only if we haven't seen it. Duplicate call sites in a method
        // body could cause duplicate edges.
        if (!cg.hasEdge(m1, m2)) {
          cg.addEdge(m1, m2);
        }
      }
    }
  }

  /**
   * Given a method signature, look at its body. Find all call sites. Then for
   * each call site, find all possible invocations
   * via polymorphism.
   */
  private ArrayList<MethodSignature> findSignaturesInBody(MethodSignature methodSig) {
    // This method is expecting a method signature that is in the view. If you see
    // this warning, something is wrong.
    if (!view.getMethod(methodSig).isPresent()) {
      System.out.println("WARNING: Couldn't find the method " + methodSig + " in the view.");
      return new ArrayList<MethodSignature>();
    }

    // We know it is defined, so we can use get.
    JavaSootMethod method = view.getMethod(methodSig).get();

    // If there's no body, then just return an empty list.
    if (!method.hasBody())
      return new ArrayList<MethodSignature>();

    // Now we gather all statements in the body.
    ArrayList<MethodSignature> ms = new ArrayList<MethodSignature>();
    for (Stmt stmt : method.getBody().getStmts()) {
      // Three possibilities:
      // (1) we have an invoke statement.
      // (2) we have an assign statement with an invocation on the righthand side.
      // (3) none of the above.
      AbstractInvokeExpr invocationExpression = stmt instanceof JInvokeStmt ? ((JInvokeStmt) stmt).getInvokeExpr()
          : null;
      invocationExpression = (stmt instanceof JAssignStmt)
          && (((JAssignStmt) stmt).getRightOp() instanceof AbstractInvokeExpr)
              ? (AbstractInvokeExpr) ((JAssignStmt) stmt).getRightOp()
              : invocationExpression;

      if (invocationExpression != null) {
        ms.addAll(findPolymorphicMethodSignatures(invocationExpression.getMethodSignature()));
      }
    }

    return ms;
  }

  private ArrayList<MethodSignature> findPolymorphicMethodSignatures(MethodSignature targetMethodSig) {
    // First thing to do is to get the actual method signature. In most cases, the
    // method is defined by the declared class.
    // otherwise, there are two other options. (1) the method is defined in a parent
    // class or (2) the method is defined as
    // a default method by an interface. Wrote helpers to take care of this.

    // Check if the class is valid.
    JavaSootClass possibleTargetClass = null;
    if (!view.getClass(targetMethodSig.getDeclClassType()).isPresent()) {
      return new ArrayList<MethodSignature>();
    } else {
      possibleTargetClass = view.getClass(targetMethodSig.getDeclClassType()).get();
    }

    // We look for a possible target.
    MethodSignature possibleTargetMethodSig = null;

    // First, is our method defined in the declared class?
    if (view.getMethod(targetMethodSig).isPresent()) {
      possibleTargetMethodSig = targetMethodSig;
    }

    // If we still don't have a valid target, try searching for an implementation in
    // the superclasses.
    if (possibleTargetMethodSig == null) {
      possibleTargetMethodSig = findMethodInAncestor(possibleTargetClass, targetMethodSig);
    }

    // TODO: Add a case here to check for a default method in an interface.

    if (possibleTargetMethodSig == null)
      return new ArrayList<MethodSignature>();
    else
      targetMethodSig = possibleTargetMethodSig;

    // Now we know the method exists in the view. What next?
    // First, let's double check that the class is in the hierarchy.
    TypeHierarchy h = view.getTypeHierarchy();
    ClassType targetClass = targetMethodSig.getDeclClassType();
    if (!h.contains(targetClass)) {
      System.out.println("WARNING: could not find the class: " + targetClass);
      return new ArrayList<MethodSignature>();
    }

    // Now we want to get a list of all subclasses.
    // TODO: Is this correct for interfaces?
    ArrayList<ClassType> subs = new ArrayList<ClassType>();
    if (h.isInterface(targetClass))
      subs.addAll(h.implementersOf(targetClass).collect(Collectors.toCollection(ArrayList::new)));
    else {
      subs.addAll(h.subclassesOf(targetClass).collect(Collectors.toCollection(ArrayList::new)));
    }

    // Now we collect all possible call sites (method signatures).
    ArrayList<MethodSignature> foundMethodSignatures = new ArrayList<MethodSignature>();

    // TODO: There should be types of methods we don't want to add. Write a helper
    // to determine these and don't
    // add the target if it satifies these conditions.
    if (true) {
      foundMethodSignatures.add(targetMethodSig);
    }

    for (ClassType sub : subs) {
      // We can skip interfaces.
      if (view.getClass(sub).get().isInterface())
        continue;

      for (JavaSootMethod possibleFoundMethodSignature : view.getClass(sub).get().getMethods()) {

        if (possibleFoundMethodSignature.getSignature().getSubSignature().equals(targetMethodSig.getSubSignature()))
          foundMethodSignatures.add(possibleFoundMethodSignature.getSignature());
      }
    }

    // System.out.println("For a method " + targetMethodSig + " the following
    // possibilities " + foundMethodSignatures);
    return foundMethodSignatures;
  }

  private MethodSignature findMethodInAncestor(JavaSootClass currentClass, MethodSignature targetMethodSignature) {
    // Is there a parent?
    if (!currentClass.getSuperclass().isPresent())
      return null;

    // And is the parent in the view?
    JavaClassType parentClassType = currentClass.getSuperclass().get();
    if (!view.getClass(parentClassType).isPresent()) {
      return null;
    }

    // Now we know that parent exists AND is in the view. Does it have the method we
    // are looking for?
    JavaSootClass parentClass = view.getClass(parentClassType).get();
    if (parentClass.getMethod(targetMethodSignature.getSubSignature()).isPresent()) {
      return parentClass.getMethod(targetMethodSignature.getSubSignature()).get().getSignature();
    }

    // If not, trust the recursion fairy.
    return findMethodInAncestor(parentClass, targetMethodSignature);
  }
}

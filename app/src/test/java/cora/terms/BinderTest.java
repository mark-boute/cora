/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import charlie.exceptions.*;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.types.TypeFactory;
import cora.terms.position.*;

public class BinderTest extends TermTestFoundation {
  @Test
  public void testNullName() {
    assertThrows(NullInitialisationError.class, () -> new Binder(null, baseType("o")));
  }

  @Test
  public void testNullType() {
    assertThrows(NullInitialisationError.class, () -> new Binder("x", null));
  }

  @Test
  public void testRootRequest() {
    Variable x = new Binder("x", baseType("o"));
    assertThrows(InappropriatePatternDataError.class, () -> x.queryRoot());
  }

  @Test
  public void testSubtermRequest() {
    Variable x = new Binder("x", baseType("o"));
    assertThrows(IndexingError.class, () -> x.queryArgument(1));
  }

  @Test
  public void testNullSubstitution() {
    Term t = new Binder("x", baseType("Int"));
    assertThrows(NullPointerException.class, () -> t.substitute(null));
  }

  @Test
  public void testNullMatch1() {
    Term t = new Binder("x", baseType("Int"));
    assertThrows(NullPointerException.class, () -> t.match(constantTerm("37", baseType("Int")), null));
  }

  @Test
  public void testNullMatch2() {
    Term t = new Binder("x", baseType("Int"));
    Substitution subst = new Subst();
    assertThrows(NullPointerException.class, () -> t.match(null, subst));
  }

  @Test
  public void testBaseVariableApplication() {
    Term t = new Binder("x", baseType("Int"));
    assertThrows(ArityError.class, () -> t.apply(t));
  }

  @Test
  public void testIllegalTypeApplication() {
    Term t = new Binder("x", arrowType("a", "b"));
    Term q = constantTerm("c", baseType("b"));
    assertThrows(TypingError.class, () -> t.apply(q));
  }

  @Test
  public void testTermVarBasics() {
    Variable x = new Binder("x", baseType("o"));
    Variable other = new Binder("x", baseType("o"));
    Term s = x;
    assertTrue(s.isVariable());
    assertTrue(s.isVarTerm());
    assertFalse(s.isConstant());
    assertFalse(s.isFunctionalTerm());
    assertTrue(s.queryVariable().equals(x));
    assertTrue(s.queryHead().equals(x));
    assertTrue(s.toString().equals("x"));
    assertTrue(s.numberArguments() == 0);
    assertTrue(s.queryArguments().size() == 0);
    assertTrue(s.isPattern());
    assertFalse(s.isFirstOrder());
    assertFalse(s.isApplication());
    assertFalse(s.isApplicative());
    assertFalse(s.isClosed());
    assertFalse(s.isGround());
    assertTrue(s.refreshBinders() == s);
    assertTrue(x.isBinderVariable());
    assertTrue(x.queryIndex() != other.queryIndex());
    Variable z = new Binder("z", arrowType("o", "o"));
    assertFalse(z.isFirstOrder());
    assertFalse(z.isApplicative());
    assertTrue(z.isBinderVariable());
    assertTrue(z.isPattern());
    assertTrue(z.apply(x).equals(new Application(z, x)));
    assertTrue(x.compareTo(x) == 0);
    assertTrue(x.compareTo(z) == -1);
    assertTrue(x.compareTo(new Var("y", baseType("o"))) == 1);
  }

  @Test
  public void testFunctions() {
    FunctionSymbol a = new Constant("a", baseType("aa"));
    TreeSet<FunctionSymbol> symbols = new TreeSet<FunctionSymbol>();
    Variable x = new Binder("x", baseType("bb"));
    x.storeFunctionSymbols(symbols);
    assertTrue(symbols.size() == 0);
    symbols.add(a);
    x.storeFunctionSymbols(symbols);
    assertTrue(symbols.size() == 1);
    assertTrue(symbols.contains(a));
  }

  @Test
  public void testTheory() {
    Variable x = new Binder("x", baseType("aa"));
    Variable y = new Binder("y", TypeFactory.boolSort);
    assertFalse(x.isTheoryTerm());
    assertTrue(y.isTheoryTerm());
    assertFalse(y.isValue());
    assertTrue(y.toValue() == null);
  }

  @Test
  public void testTermVarFreeReplaceables() {
    Variable x = new Binder("x", baseType("oo"));
    ReplaceableList lst = x.freeReplaceables();
    assertTrue(lst.size() == 1);
    assertTrue(lst.contains(x));
    assertTrue(x.boundVars().size() == 0);
  }

  @Test
  public void testTermVarVars() {
    Variable x = new Binder("x", baseType("oo"));
    Environment<Variable> vars = x.vars();
    int counter = 0;
    for (Variable v : vars) {
      counter++;
      assertTrue(counter == 1);
      assertTrue(v == x);
    }
  }

  @Test
  public void testTermVarEquality() {
    Term s1 = new Binder("x", baseType("o"));
    Term s2 = new Binder("x", baseType("o"));
    Term s3 = new Var("x", baseType("o"));
    assertTrue(s1.equals(s1));
    assertFalse(s1.equals(s2));
    assertFalse(s1.equals(null));
    assertFalse(s1.equals(s3));
    assertFalse(s2.equals(s3));
  }

  @Test
  public void testAlpaEquality() {
    Variable x = new Binder("x", baseType("o"));
    Variable z = new Binder("z", baseType("o"));
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    assertFalse(x.alphaEquals(z, mu, xi, 2));
    mu.put(x, 3);
    assertFalse(x.alphaEquals(z, mu, xi, 4));
    xi.put(z, 3);
    assertTrue(x.alphaEquals(z, mu, xi, 4));
    mu.remove(x);
    assertFalse(x.alphaEquals(z, mu, xi, 4));
    mu.put(x, 2);
    assertFalse(x.alphaEquals(z, mu, xi, 4));
    assertFalse(x.alphaEquals(x, mu, xi, 4));
    assertFalse(z.alphaEquals(z, mu, xi, 4));
    assertTrue(x.alphaEquals(x, xi, xi, 5));
  }

  @Test
  public void testVarOrFunctionalTerm() {
    Term s1 = new Binder("x", baseType("o"));
    Term s2 = constantTerm("x", baseType("o"));
    assertFalse(s1.equals(s2));
    assertTrue(s1.toString().equals(s2.toString()));
  }

  @Test
  public void testSubterms() {
    Term s = new Binder("x", baseType("o"));
    List<Pair<Term,Position>> lst = s.querySubterms();
    assertTrue(lst.size() == 1);
    assertTrue(lst.get(0).fst() == s);
    assertTrue(lst.get(0).snd().toString().equals("ε"));
  }

  @Test
  public void testPositions() {
    Term s = new Binder("x", arrowType("a", "b"));
    assertTrue(s.queryPositions(true).size() == 1);
    assertTrue(s.queryPositions(false).size() == 1);
    assertTrue(s.queryPositions(false).get(0).toString().equals("ε"));
  }

  @Test
  public void testSubtermGood() {
    Term s = new Binder("x", baseType("o"));
    Position p = Position.empty;
    assertTrue(s.querySubterm(p).equals(s));
  }

  @Test
  public void testSubtermBad() {
    Term s = new Binder("x", baseType("o"));
    Position p = new ArgumentPos(1, Position.empty);
    assertThrows(IndexingError.class, () -> s.querySubterm(p));
  }

  @Test
  public void testHeadSubtermBad() {
    Term s = new Binder("x", baseType("o"));
    Position p = new FinalPos(1);
    assertThrows(IndexingError.class, () -> s.querySubterm(p));
  }

  @Test
  public void testAbstractionSubtermRequest() {
    Term s = new Binder("x", arrowType("o", "O"));
    assertThrows(InappropriatePatternDataError.class, () -> s.queryAbstractionSubterm());
  }

  @Test
  public void testSubtermReplacementGood() {
    Term s = new Binder("x", baseType("a"));
    Term t = twoArgVarTerm();
    Position p = Position.empty;
    assertTrue(s.replaceSubterm(p, t).equals(t));
    assertTrue(s.toString().equals("x"));
  }

  @Test
  public void testSubtermReplacementBad() {
    Term s = new Binder("x", baseType("o"));
    Position p = new ArgumentPos(1, Position.empty);
    assertThrows(IndexingError.class, () -> s.replaceSubterm(p, twoArgVarTerm()));
  }

  @Test
  public void testHeadSubtermReplacementBad() {
    Term s = new Binder("x", baseType("o"));
    Position p = new FinalPos(3);
    assertThrows(IndexingError.class, () -> s.replaceSubterm(p, twoArgVarTerm()));
  }

  @Test
  public void testSubstituting() {
    Variable x = new Binder("x", baseType("Int"));
    Variable y = new Binder("y", baseType("Int"));
    Variable z = new Binder("z", baseType("Bool"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.extend(y, x); 
    assertTrue(x.substitute(gamma).equals(xterm));
    assertTrue(y.substitute(gamma).equals(x));
    assertTrue(z.substitute(gamma).equals(z));
  }

  @Test
  public void testMatchingNoMappingBinder() {
    Variable x = new Binder("x", baseType("a"));
    Term t = twoArgVarTerm();
    Subst gamma = new Subst();
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchingNoMappingNonBinder() {
    Variable x = new Binder("x", baseType("a"));
    Term t = twoArgVarTerm();
    Subst gamma = new Subst();
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchingExistingMapping() {
    Variable x = new Binder("x", baseType("a"));
    Term t = twoArgVarTerm();
    Subst gamma = new Subst(x, t);
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchingConflictingMapping() {
    Variable x = new Binder("x", baseType("a"));
    Term t = twoArgVarTerm();
    Term q = new Binder("y", baseType("a"));
    Subst gamma = new Subst(x, q);
    assertTrue(x.match(t, gamma) != null);
    assertTrue(gamma.get(x).equals(q));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchingBadType() {
    Variable x = new Binder("x", baseType("a"));
    Term t = constantTerm("u", baseType("b"));
    Subst gamma = new Subst();
    assertTrue(x.match(t, gamma) != null);
  }
}


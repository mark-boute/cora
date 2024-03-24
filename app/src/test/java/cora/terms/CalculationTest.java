/**************************************************************************************************
 Copyright 2023 Cynthia Kop

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
import java.util.ArrayList;
import java.util.TreeSet;
import charlie.exceptions.*;
import charlie.types.TypeFactory;
import charlie.types.Type;
import cora.terms.position.*;

public class CalculationTest extends TermTestFoundation {
  @Test
  public void testBasics() {
    CalculationSymbol p = TheoryFactory.plusSymbol;
    CalculationSymbol t = TheoryFactory.timesSymbol;
    CalculationSymbol a = TheoryFactory.andSymbol;
    CalculationSymbol o = TheoryFactory.orSymbol;
    assertFalse(p.isVariable());
    assertTrue(t.isConstant());
    assertTrue(a.isFunctionalTerm());
    assertFalse(o.isVarTerm());
    assertFalse(p.isApplication());
    assertFalse(t.isAbstraction());
    assertFalse(a.isMetaApplication());
    assertFalse(o.isBetaRedex());
    assertTrue(p.isGround());
    assertTrue(t.isClosed());
    assertTrue(a.isTrueTerm());
    assertTrue(o.isTheoryTerm());
    assertTrue(p.isTheorySymbol());
    assertFalse(t.isValue());
    assertTrue(a.numberArguments() == 0);
    assertTrue(o.numberMetaArguments() == 0);
    assertTrue(p.queryArguments().size() == 0);
    assertTrue(t.queryHead() == t);
    assertTrue(a.queryRoot() == a);
    assertTrue(o.toValue() == null);
    assertTrue(p.toCalculationSymbol() == p);
    assertFalse(t.isFirstOrder());
    assertTrue(a.isPattern());
    assertTrue(o.isApplicative());
    assertTrue(p.queryPositions(false).size() == 1);
    assertTrue(t.queryPositions(true).size() == 1);
    assertTrue(a.vars().size() == 0);
    assertTrue(o.mvars().size() == 0);
    assertTrue(p.freeReplaceables().size() == 0);
  }

  @Test
  public void testStore() {
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    CalculationSymbol d = TheoryFactory.divSymbol;
    d.storeFunctionSymbols(set);
    assertTrue(set.size() == 1);
    assertTrue(set.contains(d));
  }

  @Test
  public void testVariableRequest() {
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    assertThrows(InappropriatePatternDataError.class, () -> plus.queryVariable());
  }

  @Test
  public void testAbstractionSubtermRequest() {
    FunctionSymbol times = TheoryFactory.timesSymbol;
    assertThrows(InappropriatePatternDataError.class, () -> times.queryAbstractionSubterm());
  }

  @Test
  public void testArgumentPositionRequest() {
    FunctionSymbol a = TheoryFactory.andSymbol;
    assertThrows(IndexingError.class, () -> a.querySubterm(new ArgumentPos(1, Position.empty)));
  }

  @Test
  public void testHeadPositionRequest() {
    FunctionSymbol o = TheoryFactory.orSymbol;
    assertThrows(IndexingError.class, () -> o.querySubterm(new FinalPos(1)));
  }

  @Test
  public void testBadPositionReplacement() {
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    assertThrows(IndexingError.class, () ->
      plus.replaceSubterm(new ArgumentPos(1, Position.empty), new Constant("a", baseType("a"))));
  }
}

/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rewriting;

import java.util.Collection;
import java.util.TreeMap;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.terms.FunctionSymbol;

/** A finite set of user-defined symbols, with no duplicate names. */
public class Alphabet {
  private final TreeMap<String,FunctionSymbol> _symbols;

  /**
   * Create an alphabet with the given symbols.
   * Duplicate occurrences of the same function symbol are removed; duplicate occurrences of the
   * same type that are not the same symbol cause a TypingError to be produced.
   */
  public Alphabet(Collection<FunctionSymbol> symbols) {
    _symbols = new TreeMap<String,FunctionSymbol>();
    if (symbols == null) throw new NullInitialisationError("Alphabet", "symbols list");
    for (FunctionSymbol f : symbols) {
      if (f == null) throw new NullInitialisationError("Alphabet", "a symbol");
      add(f);
    }
  }

  public Alphabet copy() {
    return this;  // the current implementation is immutable, so we can safely do this;
                  // change to do a deep copy if this alphabet is ever made mutable!
  }

  /**
   * Adds a symbol to the current Alphabet. ONLY to be called from constructors (or otherwise
   * during the setup of an Alphabet), since calling it later would violate immutability.
   */
  private void add(FunctionSymbol symbol) {
    FunctionSymbol existing = _symbols.get(symbol.queryName());
    if (existing == null) _symbols.put(symbol.queryName(), symbol);
    else if (!existing.equals(symbol)) {
      throw new TypingError("Alphabet", "add", "duplicate occurrence of " +
        symbol.queryName(), existing.queryType().toString(), symbol.queryType().toString());
    }
  }

  /** Returns the FunctionSymbol with the given name if it exists, or null otherwise. */
  public FunctionSymbol lookup(String name) {
    return _symbols.get(name);
  }

  /** Returns the set of all function symbols occurring in the alphabet. */
  public Collection<FunctionSymbol> getSymbols() {
    return _symbols.values();
  }

  /** Returns a pleasant-to-read string representation of the current alphabet. */
  public String toString() {
    StringBuilder ret = new StringBuilder("");
    for (FunctionSymbol symbol : _symbols.values()) {
      ret.append(symbol.queryName());
      ret.append(" : ");
      ret.append(symbol.queryType());
      ret.append("\n");
    }
    return ret.toString();
  }
}

/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.parser.lib;

import charlie.util.UserException;

/**
 * A LexerException is an Exception that occurs while trying to tokenise a file or string.
 * Since this is information that will likely end up being shown to the user, we inherit
 * UserException so that it may be caught and handled as such, even though we only work with
 * strings (as lexer exceptions typically show only input that comes directly from the user).
 */
public class LexerException extends UserException {
  private Token _token;

  public LexerException(Token token, String message) {
    super(token.getPosition(), ": ", message);
    _token = token;
  }

  public Token queryToken() {
    return _token;
  }

  public String queryMainMessage() {
    return queryComponent(2).toString();
  }
}


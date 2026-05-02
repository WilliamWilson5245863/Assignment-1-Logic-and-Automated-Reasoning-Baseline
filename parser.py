"""
Parser for first-order logic formulas.
Supports standard operators and quantifiers.
"""

import re
from typing import List, Tuple
from formula import (
    Formula, Atom, Negation, Conjunction, Disjunction, Implication,
    UniversalQuantifier, ExistentialQuantifier
)


class Parser:
    """Parses first-order logic formulas from text."""
    
    def __init__(self, formula_str: str):
        self.formula_str = formula_str.strip()
        self.pos = 0
    
    def parse(self) -> Formula:
        """Parse a formula from the input string."""
        self.pos = 0
        formula = self.parse_implication()
        if self.pos < len(self.formula_str):
            raise SyntaxError(f"Unexpected character at position {self.pos}")
        return formula
    
    def parse_implication(self) -> Formula:
        """Parse implication (lowest precedence): A -> B."""
        left = self.parse_disjunction()
        
        while self.consume_operator('->'):
            right = self.parse_disjunction()
            left = Implication(left, right)
        
        return left
    
    def parse_disjunction(self) -> Formula:
        """Parse disjunction: A | B or A ∨ B."""
        left = self.parse_conjunction()
        
        while self.consume_operator('|') or self.consume_operator('∨'):
            right = self.parse_conjunction()
            left = Disjunction(left, right)
        
        return left
    
    def parse_conjunction(self) -> Formula:
        """Parse conjunction: A & B or A ∧ B."""
        left = self.parse_prefix()
        
        while self.consume_operator('&') or self.consume_operator('∧'):
            right = self.parse_prefix()
            left = Conjunction(left, right)
        
        return left
    
    def parse_prefix(self) -> Formula:
        """
        Parse prefix operators: negation (~, ¬) and quantifiers (∀, ∃).
        All prefix operators are handled at the same level to support:
        - ~∀x P(x)  (negation of quantified formula)
        - ∀x ~P(x)  (quantifier with negated body)
        - ~~P(x)    (double negation)
        """
        # Handle negation
        if self.consume_operator('~') or self.consume_operator('¬'):
            formula = self.parse_prefix()  # Recursive to handle ~~, ~∀, etc.
            return Negation(formula)
        
        # Handle universal quantifier
        if self.consume_keyword('forall') or self.consume_keyword('∀'):
            var = self.parse_variable()
            formula = self.parse_prefix()  # Recursive to handle ∀∀, ∀¬, etc.
            return UniversalQuantifier(var, formula)
        
        # Handle existential quantifier
        if self.consume_keyword('exists') or self.consume_keyword('∃'):
            var = self.parse_variable()
            formula = self.parse_prefix()  # Recursive to handle ∃∃, ∃¬, etc.
            return ExistentialQuantifier(var, formula)
        
        # No prefix operator, parse primary
        return self.parse_primary()
    
    def parse_primary(self) -> Formula:
        """Parse primary formula: atom or (formula)."""
        self.skip_whitespace()
        
        # Parenthesized formula
        if self.peek() == '(':
            self.pos += 1
            formula = self.parse_implication()
            self.skip_whitespace()
            if self.pos >= len(self.formula_str) or self.formula_str[self.pos] != ')':
                raise SyntaxError(f"Expected ')' at position {self.pos}")
            self.pos += 1
            return formula
        
        # Atom
        return self.parse_atom()
    
    def parse_atom(self) -> Formula:
        """Parse an atom: predicate or predicate(term1, term2, ...)."""
        self.skip_whitespace()
        
        # Parse predicate name
        if self.pos >= len(self.formula_str):
            raise SyntaxError("Unexpected end of input")
        
        predicate = ""
        while self.pos < len(self.formula_str) and (self.formula_str[self.pos].isalnum() or self.formula_str[self.pos] == '_'):
            predicate += self.formula_str[self.pos]
            self.pos += 1
        
        if not predicate:
            raise SyntaxError(f"Expected predicate name at position {self.pos}")
        
        self.skip_whitespace()
        
        # Check for arguments
        if self.pos < len(self.formula_str) and self.formula_str[self.pos] == '(':
            self.pos += 1
            terms = self.parse_terms()
            self.skip_whitespace()
            if self.pos >= len(self.formula_str) or self.formula_str[self.pos] != ')':
                raise SyntaxError(f"Expected ')' at position {self.pos}")
            self.pos += 1
            return Atom(predicate, terms)
        
        # Propositional atom (no arguments)
        return Atom(predicate, [])
    
    def parse_terms(self) -> List[str]:
        """Parse comma-separated terms."""
        terms = []
        
        while True:
            self.skip_whitespace()
            if self.pos >= len(self.formula_str) or self.formula_str[self.pos] == ')':
                break
            
            term = self.parse_term()
            terms.append(term)
            
            self.skip_whitespace()
            if self.pos >= len(self.formula_str) or self.formula_str[self.pos] != ',':
                break
            
            self.pos += 1  # consume comma
        
        return terms
    
    def parse_term(self) -> str:
        """Parse a term (variable or constant)."""
        self.skip_whitespace()
        
        if self.pos >= len(self.formula_str):
            raise SyntaxError("Expected term at end of input")
        
        term = ""
        while self.pos < len(self.formula_str) and (self.formula_str[self.pos].isalnum() or self.formula_str[self.pos] == '_'):
            term += self.formula_str[self.pos]
            self.pos += 1
        
        if not term:
            raise SyntaxError(f"Expected term at position {self.pos}")
        
        return term
    
    def parse_variable(self) -> str:
        """Parse a variable name."""
        self.skip_whitespace()
        return self.parse_term()
    
    def consume_operator(self, op: str) -> bool:
        """Try to consume an operator."""
        self.skip_whitespace()
        if self.formula_str[self.pos:self.pos+len(op)] == op:
            self.pos += len(op)
            return True
        return False
    
    def consume_keyword(self, keyword: str) -> bool:
        """Try to consume a keyword (whole word only)."""
        self.skip_whitespace()
        end_pos = self.pos + len(keyword)
        if self.formula_str[self.pos:end_pos] == keyword:
            # Check word boundary
            if end_pos < len(self.formula_str) and (self.formula_str[end_pos].isalnum() or self.formula_str[end_pos] == '_'):
                return False
            self.pos = end_pos
            return True
        return False
    
    def peek(self) -> str:
        """Peek at current character without consuming."""
        self.skip_whitespace()
        if self.pos < len(self.formula_str):
            return self.formula_str[self.pos]
        return ''
    
    def skip_whitespace(self):
        """Skip whitespace characters."""
        while self.pos < len(self.formula_str) and self.formula_str[self.pos].isspace():
            self.pos += 1


def parse_formula(formula_str: str) -> Formula:
    """Parse a formula from a string."""
    parser = Parser(formula_str)
    return parser.parse()


def parse_formulas_from_file(filename: str) -> List[Formula]:
    """Parse formulas from a file (one per line)."""
    formulas = []
    try:
        with open(filename, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if line and not line.startswith('#'):  # Skip empty lines and comments
                    try:
                        formula = parse_formula(line)
                        formulas.append(formula)
                    except SyntaxError as e:
                        print(f"Error parsing line {line_num}: {e}")
                        print(f"  Line: {line}")
    except FileNotFoundError:
        print(f"File not found: {filename}")
    
    return formulas

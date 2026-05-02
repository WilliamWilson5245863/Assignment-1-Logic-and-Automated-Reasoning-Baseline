"""
Data structures for first-order logic formulas.
Supports atoms, connectives (¬, ∧, ∨, →), and quantifiers (∀, ∃).
"""

from abc import ABC, abstractmethod
from typing import List, Set, Dict, Tuple, Optional


class Formula(ABC):
    """Base class for all first-order logic formulas."""
    
    @abstractmethod
    def __repr__(self) -> str:
        pass
    
    @abstractmethod
    def __eq__(self, other) -> bool:
        pass
    
    @abstractmethod
    def __hash__(self) -> int:
        pass
    
    @abstractmethod
    def free_variables(self) -> Set[str]:
        """Return the set of free variables in this formula."""
        pass
    
    @abstractmethod
    def substitute(self, var: str, term: str) -> 'Formula':
        """Return a new formula with all occurrences of var replaced by term."""
        pass


class Atom(Formula):
    """Atomic formula: predicate(term1, term2, ...)."""
    
    def __init__(self, predicate: str, terms: List[str]):
        self.predicate = predicate
        self.terms = terms
    
    def __repr__(self) -> str:
        if not self.terms:
            return self.predicate
        return f"{self.predicate}({','.join(self.terms)})"
    
    def __eq__(self, other) -> bool:
        return (isinstance(other, Atom) and 
                self.predicate == other.predicate and 
                self.terms == other.terms)
    
    def __hash__(self) -> int:
        return hash((self.predicate, tuple(self.terms)))
    
    def free_variables(self) -> Set[str]:
        """Variables that appear as terms in the atom (assuming lowercase = vars)."""
        return {term for term in self.terms if term and term[0].islower()}
    
    def substitute(self, var: str, term: str) -> 'Formula':
        new_terms = [term if t == var else t for t in self.terms]
        return Atom(self.predicate, new_terms)


class Negation(Formula):
    """Negation: ¬ A."""
    
    def __init__(self, formula: Formula):
        self.formula = formula
    
    def __repr__(self) -> str:
        return f"¬({self.formula})"
    
    def __eq__(self, other) -> bool:
        return isinstance(other, Negation) and self.formula == other.formula
    
    def __hash__(self) -> int:
        return hash(('¬', self.formula))
    
    def free_variables(self) -> Set[str]:
        return self.formula.free_variables()
    
    def substitute(self, var: str, term: str) -> 'Formula':
        return Negation(self.formula.substitute(var, term))


class Conjunction(Formula):
    """Conjunction: A ∧ B."""
    
    def __init__(self, left: Formula, right: Formula):
        self.left = left
        self.right = right
    
    def __repr__(self) -> str:
        return f"({self.left} ∧ {self.right})"
    
    def __eq__(self, other) -> bool:
        return (isinstance(other, Conjunction) and 
                self.left == other.left and 
                self.right == other.right)
    
    def __hash__(self) -> int:
        return hash(('∧', self.left, self.right))
    
    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()
    
    def substitute(self, var: str, term: str) -> 'Formula':
        return Conjunction(self.left.substitute(var, term),
                          self.right.substitute(var, term))


class Disjunction(Formula):
    """Disjunction: A ∨ B."""
    
    def __init__(self, left: Formula, right: Formula):
        self.left = left
        self.right = right
    
    def __repr__(self) -> str:
        return f"({self.left} ∨ {self.right})"
    
    def __eq__(self, other) -> bool:
        return (isinstance(other, Disjunction) and 
                self.left == other.left and 
                self.right == other.right)
    
    def __hash__(self) -> int:
        return hash(('∨', self.left, self.right))
    
    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()
    
    def substitute(self, var: str, term: str) -> 'Formula':
        return Disjunction(self.left.substitute(var, term),
                          self.right.substitute(var, term))


class Implication(Formula):
    """Implication: A → B."""
    
    def __init__(self, antecedent: Formula, consequent: Formula):
        self.antecedent = antecedent
        self.consequent = consequent
    
    def __repr__(self) -> str:
        return f"({self.antecedent} → {self.consequent})"
    
    def __eq__(self, other) -> bool:
        return (isinstance(other, Implication) and 
                self.antecedent == other.antecedent and 
                self.consequent == other.consequent)
    
    def __hash__(self) -> int:
        return hash(('→', self.antecedent, self.consequent))
    
    def free_variables(self) -> Set[str]:
        return self.antecedent.free_variables() | self.consequent.free_variables()
    
    def substitute(self, var: str, term: str) -> 'Formula':
        return Implication(self.antecedent.substitute(var, term),
                          self.consequent.substitute(var, term))


class UniversalQuantifier(Formula):
    """Universal quantifier: ∀x A."""
    
    def __init__(self, variable: str, formula: Formula):
        self.variable = variable
        self.formula = formula
    
    def __repr__(self) -> str:
        return f"∀{self.variable}({self.formula})"
    
    def __eq__(self, other) -> bool:
        return (isinstance(other, UniversalQuantifier) and 
                self.variable == other.variable and 
                self.formula == other.formula)
    
    def __hash__(self) -> int:
        return hash(('∀', self.variable, self.formula))
    
    def free_variables(self) -> Set[str]:
        free = self.formula.free_variables()
        free.discard(self.variable)
        return free
    
    def substitute(self, var: str, term: str) -> 'Formula':
        # Don't substitute bound variables
        if var == self.variable:
            return self
        return UniversalQuantifier(self.variable, self.formula.substitute(var, term))


class ExistentialQuantifier(Formula):
    """Existential quantifier: ∃x A."""
    
    def __init__(self, variable: str, formula: Formula):
        self.variable = variable
        self.formula = formula
    
    def __repr__(self) -> str:
        return f"∃{self.variable}({self.formula})"
    
    def __eq__(self, other) -> bool:
        return (isinstance(other, ExistentialQuantifier) and 
                self.variable == other.variable and 
                self.formula == other.formula)
    
    def __hash__(self) -> int:
        return hash(('∃', self.variable, self.formula))
    
    def free_variables(self) -> Set[str]:
        free = self.formula.free_variables()
        free.discard(self.variable)
        return free
    
    def substitute(self, var: str, term: str) -> 'Formula':
        # Don't substitute bound variables
        if var == self.variable:
            return self
        return ExistentialQuantifier(self.variable, self.formula.substitute(var, term))


class Sequent:
    """Represents a sequent: Γ ⊢ Δ where Γ and Δ are lists of formulas."""
    
    def __init__(self, antecedents: Optional[List[Formula]] = None, 
                 consequents: Optional[List[Formula]] = None):
        self.antecedents = antecedents or []
        self.consequents = consequents or []
    
    def __repr__(self) -> str:
        left = ", ".join(str(f) for f in self.antecedents) if self.antecedents else ""
        right = ", ".join(str(f) for f in self.consequents) if self.consequents else ""
        return f"{left} ⊢ {right}"
    
    def __eq__(self, other) -> bool:
        return (isinstance(other, Sequent) and 
                self.antecedents == other.antecedents and 
                self.consequents == other.consequents)
    
    def copy(self) -> 'Sequent':
        """Return a deep copy of this sequent."""
        return Sequent(self.antecedents.copy(), self.consequents.copy())
    
    def is_initial(self) -> bool:
        """Check if this is an initial sequent (id rule: axiom)."""
        for f in self.antecedents:
            if f in self.consequents:
                return True
        return False

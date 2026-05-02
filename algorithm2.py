"""
Algorithm 2: Naive backward proof search strategy for first-order logic using LK'.
Implements the proof search algorithm with support for all LK' rules.
"""

from typing import List, Optional, Set, Tuple
from copy import deepcopy
from formula import (
    Formula, Atom, Negation, Conjunction, Disjunction, Implication,
    UniversalQuantifier, ExistentialQuantifier, Sequent
)


class DerivationTree:
    """Represents a derivation tree in LK'."""
    
    def __init__(self, sequent: Sequent, rule_name: str = "", children: List['DerivationTree'] = None):
        self.sequent = sequent
        self.rule_name = rule_name
        self.children = children or []
    
    def __repr__(self) -> str:
        return f"DerivationTree({self.sequent}, rule={self.rule_name})"
    
    def is_closed(self) -> bool:
        """Check if this branch is closed (all children are closed or this is an axiom)."""
        if not self.children:
            # Leaf node - check if it's an axiom
            return self.sequent.is_initial()
        # Internal node - all children must be closed
        return all(child.is_closed() for child in self.children)
    
    def depth(self) -> int:
        """Return the depth of this tree."""
        if not self.children:
            return 1
        return 1 + max(child.depth() for child in self.children)
    
    def print_tree(self, indent: str = "") -> str:
        """Return a string representation of the tree."""
        result = f"{indent}{self.sequent} ({self.rule_name})\n"
        for child in self.children:
            result += child.print_tree(indent + "  ")
        return result


class ProofSearch:
    """Implements Algorithm 2 - naive backward proof search for LK'."""
    
    def __init__(self, max_depth: int = 50, max_fresh_terms: int = 10):
        """
        Initialize the proof search.
        
        Args:
            max_depth: Maximum search depth to prevent infinite loops
            max_fresh_terms: Maximum number of fresh terms to generate
        """
        self.max_depth = max_depth
        self.max_fresh_terms = max_fresh_terms
        self.fresh_term_counter = 0
        self.used_terms = set()  # Track terms used for instantiation
    
    def search(self, formula: Formula) -> Optional[DerivationTree]:
        """
        Perform backward proof search for a formula.
        
        Args:
            formula: The formula to prove
        
        Returns:
            A DerivationTree if proof found, None otherwise
        """
        # Initial sequent: ⊢ A
        initial_sequent = Sequent(antecedents=[], consequents=[formula])
        self.fresh_term_counter = 0
        self.used_terms = set()
        
        result = self._search_internal(initial_sequent, depth=0)
        return result
    
    def _search_internal(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Recursive internal search function."""
        
        if depth > self.max_depth:
            return None
        
        # Check if this is an initial sequent (axiom)
        if sequent.is_initial():
            return DerivationTree(sequent, rule_name="id")
        
        # Try to apply rules from Algorithm 2
        
        # 1. Try rules that close branches: id, TR, LL
        result = self._try_identity_rule(sequent, depth)
        if result:
            return result
        
        result = self._try_true_left_rule(sequent, depth)
        if result:
            return result
        
        result = self._try_false_right_rule(sequent, depth)
        if result:
            return result
        
        # 2. Try rules without branching: ∧L, ∨R, →R, ¬L, ¬R
        result = self._try_conjunction_left(sequent, depth)
        if result:
            return result
        
        result = self._try_disjunction_right(sequent, depth)
        if result:
            return result
        
        result = self._try_implication_right(sequent, depth)
        if result:
            return result
        
        result = self._try_negation_left(sequent, depth)
        if result:
            return result
        
        result = self._try_negation_right(sequent, depth)
        if result:
            return result
        
        # 3. Try rules with branching: ∧R, ∨L, →L
        result = self._try_conjunction_right(sequent, depth)
        if result:
            return result
        
        result = self._try_disjunction_left(sequent, depth)
        if result:
            return result
        
        result = self._try_implication_left(sequent, depth)
        if result:
            return result
        
        # 4. Try quantifier rules
        result = self._try_universal_left(sequent, depth)
        if result:
            return result
        
        result = self._try_universal_right(sequent, depth)
        if result:
            return result
        
        result = self._try_existential_right(sequent, depth)
        if result:
            return result
        
        # No rule applicable
        return None
    
    # Rule implementations
    
    def _try_identity_rule(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule id: If A is in both antecedents and consequents, close the branch."""
        for formula in sequent.antecedents:
            if formula in sequent.consequents:
                return DerivationTree(sequent, rule_name="id")
        return None
    
    def _try_true_left_rule(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ⊤L (TR): Remove ⊤ from antecedents."""
        true_atom = Atom("⊤", [])
        if true_atom in sequent.antecedents:
            new_seq = sequent.copy()
            new_seq.antecedents.remove(true_atom)
            child = self._search_internal(new_seq, depth + 1)
            if child:
                return DerivationTree(sequent, rule_name="⊤L", children=[child])
        return None
    
    def _try_false_right_rule(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ⊥R (LL): Remove ⊥ from consequents."""
        false_atom = Atom("⊥", [])
        if false_atom in sequent.consequents:
            new_seq = sequent.copy()
            new_seq.consequents.remove(false_atom)
            child = self._search_internal(new_seq, depth + 1)
            if child:
                return DerivationTree(sequent, rule_name="⊥R", children=[child])
        return None
    
    def _try_conjunction_left(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ∧L: A ∧ B on left → A, B on left."""
        for i, formula in enumerate(sequent.antecedents):
            if isinstance(formula, Conjunction):
                new_seq = sequent.copy()
                new_seq.antecedents.pop(i)
                new_seq.antecedents.extend([formula.left, formula.right])
                child = self._search_internal(new_seq, depth + 1)
                if child:
                    return DerivationTree(sequent, rule_name="∧L", children=[child])
        return None
    
    def _try_disjunction_right(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ∨R: A ∨ B on right → A, B on right."""
        for i, formula in enumerate(sequent.consequents):
            if isinstance(formula, Disjunction):
                new_seq = sequent.copy()
                new_seq.consequents.pop(i)
                new_seq.consequents.extend([formula.left, formula.right])
                child = self._search_internal(new_seq, depth + 1)
                if child:
                    return DerivationTree(sequent, rule_name="∨R", children=[child])
        return None
    
    def _try_implication_right(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule →R: A → B on right → A on left, B on right."""
        for i, formula in enumerate(sequent.consequents):
            if isinstance(formula, Implication):
                new_seq = sequent.copy()
                new_seq.consequents.pop(i)
                new_seq.antecedents.append(formula.antecedent)
                new_seq.consequents.append(formula.consequent)
                child = self._search_internal(new_seq, depth + 1)
                if child:
                    return DerivationTree(sequent, rule_name="→R", children=[child])
        return None
    
    def _try_negation_left(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ¬L: ¬A on left → A on right."""
        for i, formula in enumerate(sequent.antecedents):
            if isinstance(formula, Negation):
                new_seq = sequent.copy()
                new_seq.antecedents.pop(i)
                new_seq.consequents.append(formula.formula)
                child = self._search_internal(new_seq, depth + 1)
                if child:
                    return DerivationTree(sequent, rule_name="¬L", children=[child])
        return None
    
    def _try_negation_right(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ¬R: ¬A on right → A on left."""
        for i, formula in enumerate(sequent.consequents):
            if isinstance(formula, Negation):
                new_seq = sequent.copy()
                new_seq.consequents.pop(i)
                new_seq.antecedents.append(formula.formula)
                child = self._search_internal(new_seq, depth + 1)
                if child:
                    return DerivationTree(sequent, rule_name="¬R", children=[child])
        return None
    
    def _try_conjunction_right(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ∧R: A ∧ B on right → split into two branches."""
        for i, formula in enumerate(sequent.consequents):
            if isinstance(formula, Conjunction):
                # First branch: prove A
                seq1 = sequent.copy()
                seq1.consequents[i] = formula.left
                child1 = self._search_internal(seq1, depth + 1)
                
                if child1:
                    # Second branch: prove B
                    seq2 = sequent.copy()
                    seq2.consequents[i] = formula.right
                    child2 = self._search_internal(seq2, depth + 1)
                    
                    if child2:
                        return DerivationTree(sequent, rule_name="∧R", children=[child1, child2])
        return None
    
    def _try_disjunction_left(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ∨L: A ∨ B on left → split into two branches."""
        for i, formula in enumerate(sequent.antecedents):
            if isinstance(formula, Disjunction):
                # First branch: with A
                seq1 = sequent.copy()
                seq1.antecedents[i] = formula.left
                child1 = self._search_internal(seq1, depth + 1)
                
                if child1:
                    # Second branch: with B
                    seq2 = sequent.copy()
                    seq2.antecedents[i] = formula.right
                    child2 = self._search_internal(seq2, depth + 1)
                    
                    if child2:
                        return DerivationTree(sequent, rule_name="∨L", children=[child1, child2])
        return None
    
    def _try_implication_left(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule →L: A → B on left → split into two branches."""
        for i, formula in enumerate(sequent.antecedents):
            if isinstance(formula, Implication):
                # First branch: prove the antecedent
                seq1 = sequent.copy()
                seq1.consequents.append(formula.antecedent)
                child1 = self._search_internal(seq1, depth + 1)
                
                if child1:
                    # Second branch: use the consequent
                    seq2 = sequent.copy()
                    seq2.antecedents[i] = formula.consequent
                    child2 = self._search_internal(seq2, depth + 1)
                    
                    if child2:
                        return DerivationTree(sequent, rule_name="→L", children=[child1, child2])
        return None
    
    def _try_universal_left(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ∀L: ∀x A on left → instantiate with existing constant."""
        for i, formula in enumerate(sequent.antecedents):
            if isinstance(formula, UniversalQuantifier):
                # Try instantiation with existing CONSTANTS only (not variables)
                # This prevents infinite loops from re-instantiating with variables
                constants = self._get_constants(sequent)
                terms_to_try = sorted(list(constants))
                
                # If no constants exist, use a fresh one
                if not terms_to_try:
                    terms_to_try = [f"c{self.fresh_term_counter}"]
                    self.fresh_term_counter += 1
                
                for term in terms_to_try:
                    new_seq = sequent.copy()
                    instantiated = formula.formula.substitute(formula.variable, term)
                    
                    # Skip if this instantiation already exists in antecedents
                    # This prevents infinite loops from re-adding the same formula
                    if instantiated in new_seq.antecedents:
                        continue
                    
                    new_seq.antecedents.append(instantiated)
                    child = self._search_internal(new_seq, depth + 1)
                    
                    if child:
                        return DerivationTree(sequent, rule_name=f"∀L[{term}]", children=[child])
        
        return None
    
    def _try_universal_right(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ∀R: ∀x A on right → instantiate with fresh variable."""
        for i, formula in enumerate(sequent.consequents):
            if isinstance(formula, UniversalQuantifier):
                # Create fresh variable for instantiation
                fresh_var = f"c{self.fresh_term_counter}"
                self.fresh_term_counter += 1
                
                new_seq = sequent.copy()
                instantiated = formula.formula.substitute(formula.variable, fresh_var)
                new_seq.consequents[i] = instantiated
                child = self._search_internal(new_seq, depth + 1)
                
                if child:
                    return DerivationTree(sequent, rule_name=f"∀R[{fresh_var}]", children=[child])
        
        return None
    
    def _try_existential_right(self, sequent: Sequent, depth: int) -> Optional[DerivationTree]:
        """Rule ∃R: ∃x A on right → instantiate with fresh term."""
        for i, formula in enumerate(sequent.consequents):
            if isinstance(formula, ExistentialQuantifier):
                # Try instantiation with existing terms first
                terms_to_try = self._get_instantiation_terms(sequent)
                
                for term in terms_to_try:
                    if term not in self.used_terms or term in self._get_constants(sequent):
                        new_seq = sequent.copy()
                        instantiated = formula.formula.substitute(formula.variable, term)
                        new_seq.consequents[i] = instantiated
                        self.used_terms.add(term)
                        child = self._search_internal(new_seq, depth + 1)
                        
                        if child:
                            return DerivationTree(sequent, rule_name=f"∃R[{term}]", children=[child])
                
                # Create fresh term if needed
                if self.fresh_term_counter < self.max_fresh_terms:
                    fresh_term = f"c{self.fresh_term_counter}"
                    self.fresh_term_counter += 1
                    self.used_terms.add(fresh_term)
                    
                    new_seq = sequent.copy()
                    instantiated = formula.formula.substitute(formula.variable, fresh_term)
                    new_seq.consequents[i] = instantiated
                    child = self._search_internal(new_seq, depth + 1)
                    
                    if child:
                        return DerivationTree(sequent, rule_name=f"∃R[{fresh_term}]", children=[child])
        
        return None
    
    def _get_instantiation_terms(self, sequent: Sequent) -> List[str]:
        """Get all terms available for instantiation."""
        terms = set()
        
        # Collect all terms from atoms in the sequent
        for formula in sequent.antecedents + sequent.consequents:
            self._collect_terms(formula, terms)
        
        # Add constants (uppercase terms)
        return sorted(list(terms))
    
    def _get_constants(self, sequent: Sequent) -> Set[str]:
        """Get all constants (uppercase terms) from the sequent."""
        constants = set()
        for formula in sequent.antecedents + sequent.consequents:
            self._collect_constants(formula, constants)
        return constants
    
    def _collect_terms(self, formula: Formula, terms: Set[str]):
        """Recursively collect all terms from a formula."""
        if isinstance(formula, Atom):
            terms.update(formula.terms)
        elif isinstance(formula, Negation):
            self._collect_terms(formula.formula, terms)
        elif isinstance(formula, (Conjunction, Disjunction, Implication)):
            self._collect_terms(formula.left if hasattr(formula, 'left') else formula.antecedent, terms)
            self._collect_terms(formula.right if hasattr(formula, 'right') else formula.consequent, terms)
        elif isinstance(formula, (UniversalQuantifier, ExistentialQuantifier)):
            self._collect_terms(formula.formula, terms)
    
    def _collect_constants(self, formula: Formula, constants: Set[str]):
        """Recursively collect all constants (uppercase terms) from a formula."""
        if isinstance(formula, Atom):
            for term in formula.terms:
                if term and term[0].isupper():
                    constants.add(term)
        elif isinstance(formula, Negation):
            self._collect_constants(formula.formula, constants)
        elif isinstance(formula, (Conjunction, Disjunction, Implication)):
            left = formula.left if hasattr(formula, 'left') else formula.antecedent
            right = formula.right if hasattr(formula, 'right') else formula.consequent
            self._collect_constants(left, constants)
            self._collect_constants(right, constants)
        elif isinstance(formula, (UniversalQuantifier, ExistentialQuantifier)):
            self._collect_constants(formula.formula, constants)

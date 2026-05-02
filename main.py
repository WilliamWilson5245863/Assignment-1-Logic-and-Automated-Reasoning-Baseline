"""
Main module for Algorithm 2 automated reasoning implementation.
Provides command-line interface and batch processing capabilities.
"""

import sys
import json
import time
from pathlib import Path
from typing import List, Dict, Any
from parser import parse_formula, parse_formulas_from_file
from algorithm2 import ProofSearch
from formula import Formula


class ProofSearchEngine:
    """High-level interface to the proof search algorithm."""
    
    def __init__(self, max_depth: int = 50, max_fresh_terms: int = 10):
        self.search = ProofSearch(max_depth=max_depth, max_fresh_terms=max_fresh_terms)
    
    def prove_formula(self, formula: Formula) -> Dict[str, Any]:
        """
        Attempt to prove a formula.
        
        Returns:
            A dictionary with proof status, tree, and statistics
        """
        start_time = time.time()
        try:
            tree = self.search.search(formula)
            elapsed_time = time.time() - start_time
            
            if tree and tree.is_closed():
                return {
                    'status': 'PROVED',
                    'formula': str(formula),
                    'tree': tree.print_tree(),
                    'depth': tree.depth(),
                    'is_valid': True,
                    'elapsed_time': elapsed_time
                }
            else:
                return {
                    'status': 'FAILED',
                    'formula': str(formula),
                    'tree': tree.print_tree() if tree else "No tree generated",
                    'depth': tree.depth() if tree else 0,
                    'is_valid': False,
                    'elapsed_time': elapsed_time
                }
        except Exception as e:
            elapsed_time = time.time() - start_time
            return {
                'status': 'ERROR',
                'formula': str(formula),
                'error': str(e),
                'is_valid': False,
                'elapsed_time': elapsed_time
            }
    
    def batch_process(self, formulas: List[Formula]) -> Dict[str, Any]:
        """
        Process multiple formulas and return statistics.
        
        Returns:
            Summary statistics and individual results
        """
        results = []
        proved_count = 0
        failed_count = 0
        error_count = 0
        total_depth = 0
        start_total = time.time()
        
        for i, formula in enumerate(formulas, 1):
            result = self.prove_formula(formula)
            results.append(result)
            
            if result['status'] == 'PROVED':
                proved_count += 1
                total_depth += result['depth']
            elif result['status'] == 'FAILED':
                failed_count += 1
            else:
                error_count += 1
        
        total_elapsed = time.time() - start_total
        avg_time = total_elapsed / len(formulas) if formulas else 0

        return {
            'total': len(formulas),
            'proved': proved_count,
            'failed': failed_count,
            'errors': error_count,
            'success_rate': (proved_count / len(formulas) * 100) if formulas else 0,
            'avg_depth': (total_depth / proved_count) if proved_count > 0 else 0,
            'total_elapsed': total_elapsed,
            'avg_time_per_formula': avg_time,
            'results': results
        }


def print_result(result: Dict[str, Any]):
    """Pretty print a proof result."""
    print(f"\n{'='*60}")
    print(f"Status: {result['status']}")
    print(f"Formula: {result['formula']}")
    if 'elapsed_time' in result:
        print(f"Elapsed time: {result['elapsed_time']:.6f} seconds")
    
    if result['status'] == 'PROVED':
        print(f"Depth: {result['depth']}")
        print(f"\nDerivation Tree:")
        print(result['tree'])
    elif result['status'] == 'FAILED':
        print("No proof found within search limits")
    else:
        print(f"Error: {result.get('error', 'Unknown error')}")


def print_batch_summary(summary: Dict[str, Any]):
    """Pretty print batch processing summary."""
    print(f"\n{'='*60}")
    print("BATCH PROCESSING SUMMARY")
    print(f"{'='*60}")
    print(f"Total formulas: {summary['total']}")
    print(f"Proved: {summary['proved']}")
    print(f"Failed: {summary['failed']}")
    print(f"Errors: {summary['errors']}")
    print(f"Success rate: {summary['success_rate']:.1f}%")
    if summary['avg_depth'] > 0:
        print(f"Average tree depth: {summary['avg_depth']:.2f}")
    
    print(f"\nTiming Statistics:")
    print(f"  Total elapsed: {summary['total_elapsed']:.6f} seconds")
    print(f"  Average per formula: {summary['avg_time_per_formula']:.6f} seconds")
    
    print(f"\n{'='*60}")
    for i, result in enumerate(summary['results'], 1):
        status_symbol = "✓" if result['status'] == 'PROVED' else ("✗" if result['status'] == 'FAILED' else "⚠")
        depth_info = f" (depth: {result['depth']})" if 'depth' in result and result['depth'] > 0 else ""
        print(f"{status_symbol} {i}. {result['formula']}{depth_info}")


def main():
    """Main entry point."""
    engine = ProofSearchEngine(max_depth=50, max_fresh_terms=10)
    
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python main.py <formula>              - Prove a single formula")
        print("  python main.py -f <file>              - Prove formulas from file")
        print("  python main.py -e                     - Run example formulas")
        print("\nExample formulas:")
        print("  python main.py 'p | ~p'")
        print("  python main.py 'forall x (P(x) | ~P(x))'")
        return
    
    if sys.argv[1] == '-f':
        if len(sys.argv) < 3:
            print("Error: specify input file")
            return
        
        filename = sys.argv[2]
        print(f"Reading formulas from {filename}...")
        formulas = parse_formulas_from_file(filename)
        
        if not formulas:
            print("No formulas found in file")
            return
        
        print(f"Found {len(formulas)} formulas")
        summary = engine.batch_process(formulas)
        print_batch_summary(summary)
        
        # Save results if requested
        if len(sys.argv) > 3 and sys.argv[3] == '-o':
            output_file = sys.argv[4] if len(sys.argv) > 4 else 'results.json'
            with open(output_file, 'w') as f:
                json.dump(summary, f, indent=2)
            print(f"\nResults saved to {output_file}")
    
    elif sys.argv[1] == '-e':
        print("Running example formulas...")
        examples = [
            'p | ~p',                           # Law of excluded middle
            '(p -> q) | (q -> p)',             # Always true
            'forall x (P(x) | ~P(x))',         # Quantified excluded middle
            'forall x P(x) -> exists x P(x)',  # All implies exists
            'p & q -> p',                      # Conjunction elimination
            '(p -> q) & p -> q',               # Modus ponens
            'p -> p',                          # Identity
            '~~p -> p',                        # Double negation
        ]
        
        for formula_str in examples:
            try:
                formula = parse_formula(formula_str)
                result = engine.prove_formula(formula)
                print_result(result)
            except Exception as e:
                print(f"Error parsing '{formula_str}': {e}")
    
    else:
        formula_str = sys.argv[1]
        try:
            formula = parse_formula(formula_str)
            result = engine.prove_formula(formula)
            print_result(result)
        except Exception as e:
            print(f"Error: {e}")


if __name__ == '__main__':
    main()

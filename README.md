# Real Analysis Formalizations

This repository contains formalizations of important theorems in graduate real analysis, done for practice. Below is a list of the included theorems.

# Weierstrass Approximation Theorem
Overview:
  AI-assisted (Claude Sonnet 5.5, GPT-6) formalization of the Weierstrass Approximation Theorem on the unit interval in Lean 4, from scratch by bounding the
  difference between f and its associated Bernstein polynomials.
  
  The theorem says that the polynomials are dense in C[0,1], or that any continuous function f:[0,1]->R can be approximated by a sequence of polynomials on [0,1]. The result extends to any compact subset K of R.

Requirements:
  Lean 4,
  Mathlib

Building:
  From the project directory, run:
  lake build

  # Arzelà–Ascoli Theorem
Overview:
  AI-assisted (Claude Sonnet 5.5, GPT-6) formalization of the Arzelà–Ascoli Theorem in Lean 4. The formalization is based on the proof found in https://www.math.ucdavis.edu/~hunter/book/ch2.pdf
  The proof shows precompactness is equivalent to boundedness and equicontinuity. 
  
  The theorem says compactness of a subset in C(K) is equivalent to being closed, bounded, and equicontinuous.

Requirements:
  Lean 4,
  Mathlib

Building:
  From the project directory, run:
  lake build

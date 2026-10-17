# WeierstrassApproximationTheorem

Overview:
  AI-assisted (Claude Sonnet 5.5, GPT-6) formalization of the Weierstrass Approximation Theorem on the unit interval in Lean 4, from scratch by bounding of the
  difference between f and its associated Bernstein polynomials.
  
  The result says that the polynomials are dense in C[0,1], or that any continuous function f can be approximated by a sequence of polynomials on [0,1].

Requirements:
  Lean 4,
  Mathlib

Building:
  From the project directory, run:
  lake build

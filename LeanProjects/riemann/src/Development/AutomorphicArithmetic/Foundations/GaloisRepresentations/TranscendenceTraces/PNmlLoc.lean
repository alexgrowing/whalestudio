import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nmlLoc_of :
    NmlInt → NmlNoeth → NmlLoc := by
  intro hI hN S hS h
  rcases h with h | h
  · haveI := h
    exact hI S hS
  · haveI := h
    exact hN S hS

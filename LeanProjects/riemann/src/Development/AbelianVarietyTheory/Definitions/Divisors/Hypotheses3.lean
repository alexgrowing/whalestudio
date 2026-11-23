import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DeRhamVectorExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen

namespace GlobalTheory.CovTop

structure Hypotheses3 : Prop where

  base : Hypotheses2

  g1 : GlobalTheory.Published.GrothendieckDeformation

  g4 : GlobalTheory.Published.ChowFormHyperplaneSection

theorem Hypotheses3.quoted (h : Hypotheses3) : GlobalTheory.HSCore.Quoted :=
  ⟨h.base.q6, h.base.q8, h.base.q13, h.base.q7, h.base.q10, GlobalTheory.Published.chowFormIntExists_holds, h.g4, h.base.q12⟩

end GlobalTheory.CovTop

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem numOf_eq_ofRecord (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (h1 : D.s.Del = (Del : ℚ))
    (h2 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) : GlobalTheory.RunDepth.numOf D L = ofRecord D L Del h0 := by
  have hm : (D.R.m : ℝ) ≠ 0 := by
    intro h
    have := L.etaSz_pos
    rw [h2, h, zero_mul] at this
    exact lt_irrefl _ this
  have e1 : ⌊((D.s.Del : ℚ) : ℝ)⌋₊ = Del := by
    rw [h1, Rat.cast_natCast, Nat.floor_natCast]
  have e2 : ⌊LevelStarExponents.h0 L⌋₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [h2, mul_div_cancel_left₀ _ hm]
    rw [this, Nat.floor_natCast]
  have e3 : (fun z => D.hc (GlobalTheory.RunDepth.plOf D z)) = fun z => D.hc (Formalism.BasicNotions.tauPl D z) := by
    funext z
    obtain ⟨b, t⟩ := z
    cases b <;> rfl
  unfold GlobalTheory.RunDepth.numOf ofRecord
  simp only [e1, e2, e3]

theorem numOf_Fj_eq_ofRecord :
    ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) → ∀ (j : ℕ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)), (GlobalTheory.RunDepth.numOf D L).Fj j w = (ofRecord D L Del h0).Fj j w := by
  intro D L Del h0 h1 h2 j w
  rw [numOf_eq_ofRecord D L Del h0 h1 h2]

end GlobalTheory.BigOn

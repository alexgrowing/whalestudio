import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HermLine

abbrev signLine (D : D7) (p q : ℕ) : HSp D :=
  Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral (p + q) (fun i => decide (p ≤ (i : ℕ))) p q

theorem signLine_norm (D : D7) (c : D.host.E) (p q : ℕ) (h : p + q = 1) :
    star (fun _ : Fin (signLine D p q).rank => c) ⬝ᵥ (signLine D p q).gram *ᵥ (fun _ : Fin (signLine D p q).rank => c) =
      (Examples₂.sgn (decide (p ≤ 0)) : D.host.E) * (c * star c) := by
  obtain ⟨i0, hi⟩ : ∃ i0 : Fin (p + q), (i0 : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have huniq : ∀ i : Fin (p + q), i = i0 := fun i => Fin.ext (by omega)
  show ∑ i : Fin (p + q), star c * ∑ j : Fin (p + q), (signLine D p q).gram i j * c = _
  have hsum : ∀ f : Fin (p + q) → D.host.E, ∑ i, f i = f i0 := by
    intro f
    rw [Finset.sum_eq_single i0 (fun b _ hb => absurd (huniq b) hb) (by simp)]
  rw [hsum, hsum, Examples₂.stdSpace_gram_apply, if_pos rfl, hi]
  ring

theorem exists_line_vec (D : D7) (c : D.host.E) (ε : ℤˣ) (hc : c ≠ 0) :
    ∃ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ ∧ L.SigOK ∧
      star ζ ⬝ᵥ L.gram *ᵥ ζ = ((ε : ℤ) : D.host.E) * (c * star c) ∧
      ∀ τ, L.sig τ = if ε = 1 then (1, 0) else (0, 1) := by
  have hcc : c * star c ≠ 0 := mul_ne_zero hc (star_ne_zero.2 hc)
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have hn := signLine_norm D c 1 0 rfl
    simp only [Examples₂.sgn, zero_add, nonpos_iff_eq_zero, one_ne_zero, decide_false, Bool.false_eq_true,
      if_false, one_mul] at hn
    refine ⟨signLine D 1 0, fun _ => c, ⟨rfl, ?_⟩, GlobalTheory.Ker.Inhab.sigOK_std D 1 0, ?_, fun τ => ?_⟩
    · rw [hn]; exact hcc
    · rw [hn]; simp
    · simp; rfl
  · have hn := signLine_norm D c 0 1 rfl
    simp only [Examples₂.sgn, le_refl, decide_true, if_true] at hn
    refine ⟨signLine D 0 1, fun _ => c, ⟨rfl, ?_⟩, GlobalTheory.Ker.Inhab.sigOK_std D 0 1, ?_, fun τ => ?_⟩
    · rw [hn, neg_one_mul]; exact neg_ne_zero.2 hcc
    · rw [hn]; simp
    · rw [if_neg (by decide)]; rfl

end GlobalTheory.HermLine

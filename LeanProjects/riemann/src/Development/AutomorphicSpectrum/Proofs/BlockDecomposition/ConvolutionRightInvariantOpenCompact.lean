import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem tst_finGL_inv_mul {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (u : GL (Fin a) (Af E)) (hu : u ∈ U)
    (y : GA E a) : tst U β ((finGL E a u)⁻¹ * y) = tst U β y := by
  have hinv : ((finGL E a u)⁻¹ * y)⁻¹ = y⁻¹ * finGL E a u := by
    rw [_root_.mul_inv_rev, inv_inv]
  have hfin : GeneralLinearGroup.map (pFin E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pFin E) y⁻¹ * u := by
    rw [map_mul, pFin_finGL]
  have hinf : GeneralLinearGroup.map (pInf E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pInf E) y⁻¹ := by
    rw [map_mul, pInf_finGL, mul_one]
  unfold tst ker
  rw [hinv, hfin, hinf]
  by_cases hm : GeneralLinearGroup.map (pFin E) y⁻¹ ∈ U
  · rw [if_pos (U.mul_mem hm hu), if_pos hm]
  · rw [if_neg (fun h => hm (by simpa using U.mul_mem h (U.inv_mem hu))), if_neg hm]

theorem convR_tst_mul_finGL (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ)
    (u : GL (Fin a) (Af E)) (hu : u ∈ U) (x : GA E a) :
    convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  unfold convR
  have h := integral_mul_left_eq_self (μ := μ)
    (fun y => tst U β ((finGL E a u)⁻¹ * y) * Fl (x * y)) (finGL E a u)
  simp only [inv_mul_cancel_left] at h
  simp only [tst_finGL_inv_mul U β u hu] at h
  simpa only [mul_assoc] using h

theorem convR_tst_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (u : GL (Fin a) (Af E)), u ∈ U → ∀ x : GA E a, convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  intro E _ _ _ a μ _ _ U β Fl u hu x
  exact convR_tst_mul_finGL E a μ U β Fl u hu x

end GlobalTheory.CompanionTheory.SmoothRep

import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeTrivialBoundOfBoundedZonalSphericalUnitaryStatement

noncomputable section

namespace GlobalTheory.SatBoundInert

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

theorem norm_form_le {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ)
    (hsym : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hpos : ∀ v, v ≠ 0 → 0 < (B v v).re) (u v : V)
    (h : B u u = B v v) : ‖B u v‖ ≤ (B v v).re := by
  have hnn : ∀ z, 0 ≤ (B z z).re := fun z => by
    by_cases hz : z = 0
    · simp [hz]
    · exact (hpos z hz).le
  by_cases h0 : B u v = 0
  · rw [h0, norm_zero]; exact hnn v
  have hn : (‖B u v‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h0)
  have hz := hnn (u - (B u v / (‖B u v‖ : ℂ)) • v)
  have e : B (u - (B u v / (‖B u v‖ : ℂ)) • v) (u - (B u v / (‖B u v‖ : ℂ)) • v) =
      B u u - starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v - (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) +
        (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B v v := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
    rw [hsym u v]
    ring
  have h1 : starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v = ‖B u v‖ := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul', sq]
    field_simp
  have h2 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) = ‖B u v‖ := by
    rw [div_mul_eq_mul_div, Complex.mul_conj', sq]
    field_simp
  have h3 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) = 1 := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj', sq]
    field_simp
  rw [e, h1, h2, h3, h] at hz
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, one_mul] at hz
  linarith

theorem satakeBoundInert : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert := by
  intro L _ _ _ ϖ σ q n hU V _ _ π α _ hun hsat
  obtain ⟨B, hsym, hpos, hinv⟩ := hun
  obtain ⟨x, hx⟩ := hsat.exists_vec
  have hxx : B x x ≠ 0 := fun h => by
    have := hpos x hx.1
    rw [h] at this
    simp at this
  let c : ℂ := (B x x)⁻¹
  let l : V →ₗ[ℂ] ℂ :=
    { toFun := fun y => B y x * c
      map_add' := fun a b => by simp [add_mul]
      map_smul' := fun a y => by simp [mul_assoc] }
  have hl : ∀ k ∈ KU σ n, ∀ y, l (π k y) = l y := fun k hk y => by
    show B (π k y) x * c = B y x * c
    conv_lhs => rw [← GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk]
    rw [hinv]
  have h1 : l x = 1 := mul_inv_cancel₀ hxx
  have hz := GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.isZonal_of_isSatVecU hU hx l hl h1
  have hϖ : ϖ ≠ 0 := by
    intro h
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  refine GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary GlobalTheory.InertZeta.unramDoublingInert L (Units.mk0 ϖ hϖ) σ q n hU α _ hz ⟨(B x x).re * ‖c‖, fun g => ?_⟩
  show ‖B (π g x) x * c‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_form_le B hsym hpos _ _ (hinv g x x)) (norm_nonneg _)

end GlobalTheory.SatBoundInert

end

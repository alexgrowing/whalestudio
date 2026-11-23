import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaEqProdSigmaStarSquareQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEntireOfLocallyDvd
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

noncomputable section

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem trFac_ne (z ω : ℂ) : GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ≠ 0 := Complex.exp_ne_zero _

theorem differentiable_trFac (ω : ℂ) : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω := by
  unfold GlobalTheory.EvenTheta.Fibres.trFac
  fun_prop

theorem exists_sg_mul_sq (h : IsLat Λ) {β : ℂ} (hβ : ∀ ω ∈ Λ, β * ω ∈ Λ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z := by
  have hσ := h.differentiable
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  refine exists_entire_of_locally_dvd (F := fun z => sgStar Λ (β * z) ^ 2) (S := fun z => sgStar Λ z ^ 2)
    (h.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => ?_
  by_cases hw : w ∈ Λ
  · have hT := differentiable_trFac (Λ := Λ) w
    have hT' := differentiable_trFac (Λ := Λ) (β * w)
    set D : ℂ → ℂ := fun z => u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2
      with hD_def
    have hD : Differentiable ℂ D := by
      rw [hD_def]
      have h1 : Differentiable ℂ fun z => u (z - w) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) :=
        hT'.comp (by fun_prop)
      fun_prop
    have hD0 : D w ≠ 0 := by
      simp only [hD_def, sub_self, hu0]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (trFac_ne _ _))
    set N : ℂ → ℂ := fun z => β ^ 2 * u (β * (z - w)) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w ^ 2
      with hN_def
    have hN : Differentiable ℂ N := by
      rw [hN_def]
      have h1 : Differentiable ℂ fun z => u (β * (z - w)) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w :=
        hT.comp (by fun_prop)
      fun_prop
    refine ⟨fun z => N z / D z, (hN.analyticAt w).div (hD.analyticAt w) hD0, ?_⟩
    filter_upwards [hD.continuous.continuousAt.eventually_ne hD0] with z hz
    have hz1 : u (z - w) ≠ 0 := fun h0 => hz (by simp [hD_def, h0])
    have e1 := GlobalTheory.EvenTheta.Fibres.sg_sq h hw (z - w)
    have e2 := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ w hw) (β * (z - w))
    rw [sub_add_cancel] at e1
    rw [show β * (z - w) + β * w = β * z by ring] at e2
    have t1 := trFac_ne (Λ := Λ) (z - w) w
    have t2 := trFac_ne (Λ := Λ) (β * (z - w)) (β * w)
    simp only [hN_def, hD_def]
    rw [eu (z - w)] at e1
    rw [eu (β * (z - w))] at e2
    have hz' : u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2 ≠ 0 := hz
    rw [mul_div_assoc', eq_div_iff hz']
    linear_combination u (z - w) ^ 2 * e2 - β ^ 2 * u (β * (z - w)) ^ 2 * e1
  · refine ⟨fun z => sgStar Λ (β * z) ^ 2 / sgStar Λ z ^ 2,
      (((hσ.comp (by fun_prop : Differentiable ℂ fun z => β * z)).pow 2).analyticAt w).div
        ((hσ.analyticAt w).pow 2) (pow_ne_zero 2 (hne w hw)), ?_⟩
    filter_upwards [hσ.continuous.continuousAt.eventually_ne (hne w hw)] with y hy
    field_simp

end GlobalTheory.EvenTheta.MulLat

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem val_zero (h : IsLat Λ) {β : ℂ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (eG : ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z) : G 0 = β ^ 2 := by
  have hσ := h.differentiable
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  have hGc := hG.continuous
  have hUc := hU.continuous
  have key := congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (f := fun z => u z ^ 2 * G z) (g := fun z => β ^ 2 * u (β * z) ^ 2) (by fun_prop)
    (by fun_prop) fun z hz => by
      have hz : z ≠ 0 := hz
      have e := eG z
      rw [eu, eu z] at e
      refine mul_left_cancel₀ (pow_ne_zero 2 hz) ?_
      beta_reduce
      linear_combination -e) 0
  simpa [hu0] using key

theorem sg_mul_sq : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (β : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ ∧ β * Q i ∈ Λ) ∧ ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := by
  intro Λ h β k hβ hN
  have hβ0 : β ≠ 0 := by
    rintro rfl
    norm_num at hN
    exact Nat.cast_add_one_ne_zero k hN.symm
  have hσ := h.differentiable
  have hσc := hσ.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  obtain ⟨G, hG, eG⟩ := exists_sg_mul_sq h hβ
  have hGc := hG.continuous
  have hG0 := val_zero h hG eG
  have hev : ∀ z, G (-z) = G z := fun z => by
    refine congrFun (Continuous.ext_on h.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [h.sg_neg, neg_sq, mul_neg, h.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  have hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) = G z := by
    intro ω hω z
    have hTc : Continuous fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω :=
      (differentiable_trFac ω).continuous
    refine congrFun (Continuous.ext_on h.dense_compl
      (f := fun z => G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have ea := GlobalTheory.EvenTheta.Fibres.sg_sq h hω z
    have eb := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ ω hω) (β * z)
    rw [GlobalTheory.EvenTheta.Fibres.trFac_mul hN] at eb
    have egz := eG z
    have egw := eG (z + ω)
    rw [mul_add] at egw
    beta_reduce
    linear_combination egz + eb - GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k + 2) * egw -
      G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) * ea
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.EvenTheta.exists_eq_prod_sqTh Λ h k (fun z => G z / β ^ 2)
    (hG.div_const _) (fun z => by simp only [hev]) (by simp only [hG0]; exact div_self (pow_ne_zero 2 hβ0))
    (fun ω hω z => GlobalTheory.EvenTheta.Fibres.law_of_fac h (F := fun z => G z / β ^ 2) (k := k) hω z (by
      show G (z + ω) / β ^ 2 * _ = G z / β ^ 2
      rw [div_mul_eq_mul_div, hlaw ω hω z]))
  have hfac : ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := fun z => by
    rw [eG z, ← hQe z]
    field_simp
  refine ⟨Q, fun i => ⟨hQ i, ?_⟩, hfac⟩
  refine (h.sg_eq_zero _).1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ?_)
  rw [hfac, Finset.prod_eq_zero (Finset.mem_univ i)
    ((h.sqTh_eq_zero (hQ i) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem))), mul_zero]

end GlobalTheory.EvenTheta.MulLat

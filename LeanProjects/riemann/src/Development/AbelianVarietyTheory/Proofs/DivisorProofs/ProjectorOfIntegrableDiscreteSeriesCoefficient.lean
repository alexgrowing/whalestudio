import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolariseIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfSmulHaarEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorEmbedding

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial MeasureTheory GlobalTheory.FockTensor

noncomputable section

namespace GlobalTheory.CoefProjector

variable {p q : ℕ} {T : GrpData p q}

theorem inner_opE (πU : URep T) {e : T.G → ℂ} (hi : Integrable e T.haar)
    (hc : Continuous e) (z x : πU.H) :
    inner ℂ z (opE T πU.π e x) = ∫ g, e g * inner ℂ z (πU.π g x) ∂T.haar := by
  have h : Integrable (fun g => e g • πU.π g x) T.haar := by
    refine Integrable.mono' (hi.norm.mul_const ‖x‖) (hc.smul (πU.cont x)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, πU.isom]
  unfold opE
  rw [← integral_inner h]
  simp only [inner_smul_right]

theorem continuous_eFun (D : DSRep T) (v : D.HK.V) : Continuous (eFun D v) :=
  continuous_const.mul (continuous_const.inner (D.U.cont _)).star

theorem pi_mul (πU : URep T) (g h : T.G) (x : πU.H) : πU.π (g * h) x = πU.π g (πU.π h x) := by
  rw [map_mul]; rfl

theorem eFun_inv (D : DSRep T) (v : D.HK.V) (g : T.G) : eFun D v g⁻¹ = star (eFun D v g) := by
  simp only [eFun, mcoef]
  rw [← inner_pi_left]
  simp [inner_conj_symm]

theorem fdeg_ne (D : DSRep T) : (D.fdeg : ℂ) ≠ 0 := by exact_mod_cast D.fdeg_pos.ne'

theorem integral_eFun_mul (D : DSRep T) (v : D.HK.V) (w u : D.U.H) :
    ∫ g, eFun D v g * inner ℂ w (D.U.π g u) ∂T.haar = inner ℂ (D.ι v) u * inner ℂ w (D.ι v) := by
  have h := (GlobalTheory.SchurPol.schur_polarised p q T D u w (D.ι v) (D.ι v)).2
  have h2 : ∀ g, eFun D v g * inner ℂ w (D.U.π g u) =
      (D.fdeg : ℂ) * (inner ℂ w (D.U.π g u) * star (inner ℂ (D.ι v) (D.U.π g (D.ι v)))) := by
    intro g; simp only [eFun, mcoef]; ring
  simp only [h2]
  rw [integral_const_mul, h]
  have := fdeg_ne D
  have h3 : star (inner ℂ (D.ι v) w) = inner ℂ w (D.ι v) := inner_conj_symm _ _
  rw [h3]
  field_simp

theorem opE_self (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (u : D.U.H) :
    opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v := by
  refine ext_inner_left ℂ fun w => ?_
  rw [inner_opE D.U hi (continuous_eFun D v), integral_eFun_mul, inner_smul_right]

theorem opE_selfAdjoint (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (πU : URep T)
    (x y : πU.H) :
    inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y) := by
  haveI := (GlobalTheory.HolDS.haar_unimodular p q T).2
  rw [← inner_conj_symm, inner_opE πU hi (continuous_eFun D v), inner_opE πU hi (continuous_eFun D v),
    ← integral_conj, ← integral_inv_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [map_mul, inner_conj_symm, inner_pi_left, inv_inv, eFun_inv]
  simp

theorem eFun_conv (D : DSRep T) (v : D.HK.V) (x h : T.G) :
    ∫ g, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) ∂T.haar = mcoef D v x * eFun D v h := by
  have h2 : ∀ g, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) =
      (D.fdeg : ℂ) * (eFun D v g * inner ℂ (D.U.π h (D.ι v)) (D.U.π g (D.U.π x (D.ι v)))) := by
    intro g
    have : eFun D v (x⁻¹ * (g⁻¹ * h)) =
        (D.fdeg : ℂ) * inner ℂ (D.U.π h (D.ι v)) (D.U.π g (D.U.π x (D.ι v))) := by
      simp only [eFun, mcoef]
      rw [pi_mul, pi_mul, ← inner_pi_left, ← inner_pi_left]
      congr 1
      exact inner_conj_symm _ _
    rw [this]; ring
  simp only [h2]
  rw [integral_const_mul, integral_eFun_mul]
  simp only [eFun, mcoef]
  have h3 : star (inner ℂ (D.ι v) (D.U.π h (D.ι v))) = inner ℂ (D.U.π h (D.ι v)) (D.ι v) :=
    inner_conj_symm _ _
  rw [h3]; ring

theorem opE_pi_opE (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (πU : URep T)
    (x : T.G) (y : πU.H) :
    opE T πU.π (eFun D v) (πU.π x (opE T πU.π (eFun D v) y)) =
      mcoef D v x • opE T πU.π (eFun D v) y := by
  have hc := continuous_eFun D v
  refine ext_inner_left ℂ fun z => ?_
  rw [inner_smul_right, inner_opE πU hi hc, inner_opE πU hi hc z y, ← integral_const_mul]
  have h1 : ∀ g, eFun D v g * inner ℂ z (πU.π g (πU.π x (opE T πU.π (eFun D v) y))) =
      ∫ h, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) * inner ℂ z (πU.π h y) ∂T.haar := by
    intro g
    have e1 : inner ℂ z (πU.π g (πU.π x (opE T πU.π (eFun D v) y))) =
        inner ℂ (πU.π (g * x)⁻¹ z) (opE T πU.π (eFun D v) y) := by
      rw [inner_pi_left, inv_inv, pi_mul]
    rw [e1, inner_opE πU hi hc, ← integral_const_mul, ← integral_mul_left_eq_self _ (g * x)⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    rw [pi_mul, inner_pi_pi, mul_inv_rev, mul_assoc x⁻¹, mul_assoc]
  simp only [h1]
  have hi' : Integrable (fun k => eFun D v (x⁻¹ * k)) T.haar := hi.comp_mul_left x⁻¹
  have hp := ((measurePreserving_prod_inv_mul T.haar T.haar).integrable_comp_of_integrable
    (hi.mul_prod hi'))
  have hcont : Continuous fun h : T.G × T.G => inner ℂ z (πU.π h.2 y) :=
    (continuous_const.inner (πU.cont y)).comp continuous_snd
  have hp2 := hp.mul_bdd (c := ‖z‖ * ‖y‖) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => by
      simpa [πU.isom] using norm_inner_le_norm (𝕜 := ℂ) z (πU.π h.2 y))
  rw [integral_integral_swap hp2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  rw [integral_mul_const, eFun_conv, mul_assoc]

theorem dense_orbit (D : DSRep T) (u : D.U.H) (hu : u ≠ 0) :
    DenseRange (Finsupp.linearCombination ℂ fun g : T.G => D.U.π g u) := by
  have : Dense ((LinearMap.range (Finsupp.linearCombination ℂ fun g : T.G => D.U.π g u) :
      Submodule ℂ D.U.H) : Set D.U.H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro w hw
    have h := ext_orbit D u hu (innerSL ℂ w) 0 fun g => by
      refine Submodule.inner_left_of_mem_orthogonal ?_ hw
      exact ⟨Finsupp.single g 1, by simp⟩
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f w) h
    simpa using h2
  exact this

theorem exists_intertwiner (D : DSRep T) (v : D.HK.V) (hv : ‖D.ι v‖ = 1) (πU : URep T) (ξ : πU.H)
    (hξ : ∀ g, inner ℂ ξ (πU.π g ξ) = mcoef D v g * inner ℂ ξ ξ) :
    ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  have hu : D.ι v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  set A := Finsupp.linearCombination ℂ fun g : T.G => D.U.π g (D.ι v) with hA
  set B := Finsupp.linearCombination ℂ fun g : T.G => πU.π g ξ with hB
  have hd : DenseRange A := dense_orbit D _ hu
  have hgram : ∀ g h, inner ℂ (πU.π g ξ) (πU.π h ξ) =
      inner ℂ (D.U.π g (D.ι v)) (D.U.π h (D.ι v)) * inner ℂ ξ ξ := by
    intro g h
    rw [inner_pi_left, inner_pi_left, ← pi_mul, ← pi_mul, hξ, mcoef]
  have hn : ∀ c, ‖B c‖ = ‖ξ‖ * ‖A c‖ := by
    intro c
    have h : inner ℂ (B c) (B c) = inner ℂ (A c) (A c) * inner ℂ ξ ξ := by
      simp only [hA, hB, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right, hgram, Finset.sum_mul, mul_assoc]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖B c‖ ^ 2 = (‖ξ‖ * ‖A c‖) ^ 2 := by
      rw [mul_pow, mul_comm]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'
  have hT : ∀ c, B.extendOfNorm A (A c) = B c :=
    LinearMap.extendOfNorm_eq hd ⟨‖ξ‖, fun c => (hn c).le⟩
  have hg : ∀ g, B.extendOfNorm A (D.U.π g (D.ι v)) = πU.π g ξ := fun g => by
    simpa [hA, hB] using hT (Finsupp.single g 1)
  refine ⟨B.extendOfNorm A, fun g => ext_orbit D _ hu _ _ fun h => ?_, ?_, fun x => ?_⟩
  · show B.extendOfNorm A (D.U.π g (D.U.π h (D.ι v))) = πU.π g (B.extendOfNorm A (D.U.π h (D.ι v)))
    rw [← pi_mul, hg, hg, pi_mul]
  · simpa using hg 1
  · refine hd.induction_on (p := fun x => ‖B.extendOfNorm A x‖ = ‖ξ‖ * ‖x‖) x
      (isClosed_eq (by fun_prop) (by fun_prop)) fun c => ?_
    rw [hT, hn]

theorem projector_of_integrable_coefficient :
    ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (v : D.HK.V), ‖D.ι v‖ = 1 → MeasureTheory.Integrable (eFun D v) T.haar → (∀ u, opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v) ∧ ∀ πU : URep T, (∀ x y, inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y)) ∧ (∀ g x, opE T πU.π (eFun D v) (πU.π g (opE T πU.π (eFun D v) x)) = mcoef D v g • opE T πU.π (eFun D v) x) ∧ ∀ ξ, opE T πU.π (eFun D v) ξ = ξ → ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  intro p q T D v hv hi
  refine ⟨opE_self D v hi, fun πU => ⟨opE_selfAdjoint D v hi πU, opE_pi_opE D v hi πU, fun ξ hξ => ?_⟩⟩
  refine exists_intertwiner D v hv πU ξ fun g => ?_
  have h1 := opE_selfAdjoint D v hi πU ξ (πU.π g (opE T πU.π (eFun D v) ξ))
  rw [opE_pi_opE D v hi, hξ, inner_smul_right] at h1
  exact h1

end GlobalTheory.CoefProjector

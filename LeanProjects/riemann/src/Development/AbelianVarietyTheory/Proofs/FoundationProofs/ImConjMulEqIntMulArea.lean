import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TransInv

theorem im_conj_mul_ne_zero {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 := by
  intro h0
  rw [LinearIndependent.pair_iff] at h
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have h1 := h w₂.im (-w₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := h w₂.re (-w₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := h 1 0 (by
    apply Complex.ext <;> simp <;> linarith [h1.2, h2.2])
  exact one_ne_zero h3.1

theorem im_conj_mul_mem {w₁ w₂ u v : ℂ} (hu : u ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ))
    (hv : v ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)) :
    ∃ k : ℤ, ((starRingEnd ℂ) u * v).im = k * ((starRingEnd ℂ) w₁ * w₂).im := by
  obtain ⟨a, b, rfl⟩ := AddSubgroup.mem_closure_pair.1 hu
  obtain ⟨c, d, rfl⟩ := AddSubgroup.mem_closure_pair.1 hv
  refine ⟨a * d - b * c, ?_⟩
  simp
  ring

theorem area_closure_pair {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    area (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h0 := im_conj_mul_ne_zero h
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨abs_pos.2 h0, w₁, AddSubgroup.subset_closure (by simp), w₂,
    AddSubgroup.subset_closure (by simp), rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨k, hk⟩ := im_conj_mul_mem hu hv
  rw [hk] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  rw [abs_mul]
  nlinarith [abs_nonneg ((starRingEnd ℂ) w₁ * w₂).im]

theorem im_conj_mul_eq_int_mul_area {Λ : AddSubgroup ℂ}
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    0 < area Λ ∧ ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ k : ℤ, ((starRingEnd ℂ) u * v).im = k * area Λ := by
  obtain ⟨w₁, w₂, h, rfl⟩ := hΛ
  rw [area_closure_pair h]
  refine ⟨abs_pos.2 (im_conj_mul_ne_zero h), fun u hu v hv => ?_⟩
  obtain ⟨k, hk⟩ := im_conj_mul_mem hu hv
  rcases abs_cases ((starRingEnd ℂ) w₁ * w₂).im with h1 | h1
  · exact ⟨k, by rw [hk, h1.1]⟩
  · exact ⟨-k, by rw [hk, h1.1]; push_cast; ring⟩

theorem translate_add_of_fixed {Λ : AddSubgroup ℂ} (hA : area Λ ≠ 0) (G : ℂ → ℂ) (x η : ℂ) (k : ℤ)
    (hη : ∀ z, U1 Λ η G z = G z) (hk : ((starRingEnd ℂ) η * x).im = 2 * k * area Λ) :
    U1 Λ (x + η) G = U1 Λ x G := by
  funext z
  have h := hη (z + x)
  have hA' : (area Λ : ℂ) ≠ 0 := by exact_mod_cast hA
  have hs := Complex.sub_conj ((starRingEnd ℂ) η * x)
  rw [hk, map_mul, Complex.conj_conj] at hs
  push_cast at hs
  unfold U1 at h ⊢
  rw [← h, mul_assoc (G (z + x + η)), ← Complex.exp_add, ← add_assoc]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  rw [map_add]
  field_simp
  linear_combination hs

theorem translate_sigma_star_period {Λ : AddSubgroup ℂ}
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂})
    (x ω : ℂ) (m : ℕ) (hx : (m : ℂ) * (x / 2) ∈ Λ) (hω : ω ∈ Λ) :
    U1 Λ (x + 2 * (m : ℂ) * ω) (sgStar Λ) = U1 Λ x (sgStar Λ) := by
  obtain ⟨hA, hint⟩ := im_conj_mul_eq_int_mul_area hΛ
  obtain ⟨k, hk⟩ := hint ω hω _ hx
  have hm : (m : ℂ) * ω ∈ Λ := by simpa using Λ.nsmul_mem hω m
  have h2 : 2 * (m : ℂ) * ω ∈ Λ := by
    have := Λ.add_mem hm hm
    convert this using 1
    ring
  have h3 : 2 * (m : ℂ) * ω / 2 ∈ Λ := by
    convert hm using 1
    ring
  refine translate_add_of_fixed hA.ne' _ x _ (2 * k) (fun z => ?_) ?_
  · rw [(GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.2.2 _ h2 z, if_pos h3, one_mul]
  · have e : (starRingEnd ℂ) (2 * (m : ℂ) * ω) * x =
        ((4 : ℝ) : ℂ) * ((starRingEnd ℂ) ω * ((m : ℂ) * (x / 2))) := by
      simp only [map_mul, map_ofNat, map_natCast]
      push_cast
      ring
    rw [e, Complex.im_ofReal_mul, hk]
    push_cast
    ring

theorem transInv_all : ∀ D : D7, transInv D := fun D cc δ hc x ω m _ hx hω =>
  translate_sigma_star_period (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc).1 x ω m hx hω

end GlobalTheory.TransInv

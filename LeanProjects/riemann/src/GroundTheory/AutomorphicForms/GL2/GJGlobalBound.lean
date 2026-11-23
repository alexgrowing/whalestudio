import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalTheta

open MeasureTheory Set Filter NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem integrableOn_rpow_mul_ite {A B a b σ : ℝ} (ha : -σ < a) (hb : b < -σ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * (if t < 1 then A * t ^ a else B * t ^ b)) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro ht
      by_cases h : t < 1
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (not_lt.1 h)
    · rintro (h | h)
      · exact h.1
      · linarith
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun t : ℝ => A * t ^ (σ - 1 + a)) (Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)).const_mul A
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioo
    simp only [if_pos ht.2]
    rw [Real.rpow_add ht.1]
    ring
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have h1 : IntegrableOn (fun t : ℝ => B * t ^ (σ - 1 + b)) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff one_pos).2 (by linarith)).const_mul B
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht' : ¬ t < 1 := not_lt.2 (le_of_lt ht)
    simp only [if_neg ht']
    rw [Real.rpow_add (lt_trans one_pos ht)]
    ring

theorem tsum_norm_GL_le {Ψ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (a b : Matrix (Fin n) (Fin n) 𝔸[K])
    (hs : Summable fun ξ : Matrix (Fin n) (Fin n) K => ‖Ψ (a * ratMat ξ * b)‖) :
    Summable (fun γ : GL (Fin n) K => ‖Ψ (a * ratMat (γ : Matrix (Fin n) (Fin n) K) * b)‖) ∧
      ∑' γ : GL (Fin n) K, ‖Ψ (a * ratMat (γ : Matrix (Fin n) (Fin n) K) * b)‖ ≤
        ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Ψ (a * ratMat ξ * b)‖ := by
  have hs' := hs.comp_injective (Units.val_injective (α := Matrix (Fin n) (Fin n) K))
  exact ⟨hs', Summable.tsum_le_tsum_of_inj _ Units.val_injective (fun _ _ => norm_nonneg _)
    (fun _ => le_rfl) hs' hs⟩

theorem tsum_norm_inv_eq (Ψ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (t : {r : ℝ // 0 < r})
    (x y : AdelicGLn.AdelicGL K n) :
    ∑' γ : GL (Fin n) K, ‖Ψ (((centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)⁻¹ :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ =
    ∑' γ : GL (Fin n) K, ‖Ψ (((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := by
  rw [← (Equiv.inv (GL (Fin n) K)).tsum_eq]
  refine tsum_congr fun γ => ?_
  congr 2
  simp only [Equiv.inv_apply]
  have e : (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ⁻¹ * y)⁻¹ =
      centralSection K n t⁻¹ * y⁻¹ * AdelicGLn.diagonal K n γ * x := by
    rw [map_inv (AdelicGLn.diagonal K n)]
    have e1 : (centralSection K n t * x⁻¹ * (AdelicGLn.diagonal K n γ)⁻¹ * y)⁻¹ =
        (y⁻¹ * AdelicGLn.diagonal K n γ * x) * (centralSection K n t)⁻¹ := by group
    rw [e1, ← map_inv, ← centralSection_mul_comm t⁻¹ (y⁻¹ * AdelicGLn.diagonal K n γ * x)]
    simp only [mul_assoc]
  rw [e, Units.val_mul, Units.val_mul, coe_diagonal]

theorem inv_centralSection_mul (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n)
    (γ : GL (Fin n) K) :
    (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)⁻¹ =
      centralSection K n t⁻¹ * y⁻¹ * AdelicGLn.diagonal K n γ⁻¹ * x := by
  rw [map_inv (AdelicGLn.diagonal K n)]
  have e1 : (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)⁻¹ =
      (y⁻¹ * (AdelicGLn.diagonal K n γ)⁻¹ * x) * (centralSection K n t)⁻¹ := by group
  rw [e1, ← map_inv (centralSection K n) t,
    ← centralSection_mul_comm t⁻¹ (y⁻¹ * (AdelicGLn.diagonal K n γ)⁻¹ * x)]
  simp only [mul_assoc]

theorem rpow_le_of_one_lt {s M : ℝ} (hs : 1 ≤ s) : s ^ M ≤ s ^ max M 0 :=
  Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)

theorem exists_bound_GL (hn0 : 0 < n) {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ}
    (h₁ : φ₁ ∈ cuspForms K n) (h₂ : φ₂ ∈ cuspForms K n) (N : ℝ) :
    ∃ C M D : ℝ, ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      Summable (fun γ : GL (Fin n) K => ‖Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K])‖) ∧
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ∑' γ : GL (Fin n) K, ‖Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤
        (if (t : ℝ) < 1 then C * (t : ℝ) ^ (-max M 0) else D * (t : ℝ) ^ (-N)) := by
  obtain ⟨C₁, M₁, hC₁0, hC₁⟩ := exists_bound_tsum hΦ h₁ h₂
  obtain ⟨D, -, hD⟩ := exists_decay_tsum hn0 hΦ h₁ h₂ N
  refine ⟨C₁, M₁, D, fun t x y => ?_⟩
  obtain ⟨hs, hb⟩ := hC₁ x x.2 y y.2 t
  have hGL := tsum_norm_GL_le _ _ hs
  have e : ∀ γ : GL (Fin n) K, ‖Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
      AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K])‖ =
      ‖Φ (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
          ((y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := fun γ => by
    rw [coe_mul_diagonal_mul]
  simp_rw [e]
  refine ⟨hGL.1, ?_⟩
  split_ifs with ht
  · have ht0 : (0 : ℝ) < t := t.2
    have h1 : 1 ≤ (t : ℝ)⁻¹ := (one_le_inv₀ ht0).2 ht.le
    have hmax : max 1 (t : ℝ)⁻¹ = (t : ℝ)⁻¹ := max_eq_right h1
    calc _ ≤ ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
          ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ (((centralSection K n t *
            (x : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
                ((y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ :=
          mul_le_mul_of_nonneg_left hGL.2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ C₁ * (max 1 (t : ℝ)⁻¹) ^ M₁ := hb
      _ ≤ C₁ * (t : ℝ) ^ (-max M₁ 0) := by
          rw [hmax, Real.rpow_neg ht0.le, ← Real.inv_rpow ht0.le]
          exact mul_le_mul_of_nonneg_left (rpow_le_of_one_lt h1) hC₁0
  · have := (hD x x.2 y y.2 t (not_lt.1 ht)).2
    simp_rw [e] at this
    exact this

theorem exists_bound_GL_inv (hn0 : 0 < n) {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ}
    (h₁ : φ₁ ∈ cuspForms K n) (h₂ : φ₂ ∈ cuspForms K n) (N : ℝ) :
    ∃ C M D : ℝ, ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      Summable (fun γ : GL (Fin n) K => ‖adelicMatrixFourier K Φ
        (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
          (y : AdelicGLn.AdelicGL K n))⁻¹ : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K])‖) ∧
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ∑' γ : GL (Fin n) K, ‖adelicMatrixFourier K Φ
          (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
            (y : AdelicGLn.AdelicGL K n))⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤
        (if (t : ℝ) < 1 then D * (t : ℝ) ^ N else C * (t : ℝ) ^ max M 0) := by
  have hΦh := adelicMatrixFourier_mem hΦ
  obtain ⟨C₂, M₂, hC₂0, hC₂⟩ := exists_bound_tsum hΦh h₂ h₁
  obtain ⟨D, -, hD⟩ := exists_decay_tsum hn0 hΦh h₂ h₁ N
  refine ⟨C₂, M₂, D, fun t x y => ?_⟩
  set Φh := adelicMatrixFourier K Φ
  obtain ⟨hs, hb⟩ := hC₂ y y.2 x x.2 t⁻¹
  have hGL := tsum_norm_GL_le _ _ hs
  have e : ∀ γ : GL (Fin n) K, ‖Φh (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
      AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K])‖ =
      (fun δ : GL (Fin n) K => ‖Φh (((centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
          ratMat (δ : Matrix (Fin n) (Fin n) K) *
            ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖) γ⁻¹ := fun γ => by
    simp only
    rw [inv_centralSection_mul, coe_mul_diagonal_mul]
  have hsum : Summable (fun γ : GL (Fin n) K => ‖Φh (((centralSection K n t *
      (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
        (y : AdelicGLn.AdelicGL K n))⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K])‖) := by
    simp_rw [e]
    exact (Equiv.inv (GL (Fin n) K)).summable_iff.2 hGL.1
  refine ⟨hsum, ?_⟩
  rw [tsum_norm_inv_eq]
  have ht0 : (0 : ℝ) < t := t.2
  have hti : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := Positive.coe_inv t
  split_ifs with ht
  · have h1 : 1 ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) := by
      rw [hti]
      exact (one_le_inv₀ ht0).2 ht.le
    have := (hD y y.2 x x.2 t⁻¹ h1).2
    have e2 : ∀ γ : GL (Fin n) K, ‖Φh ((centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K])‖ =
        ‖Φh (((centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
            ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := fun γ => by
      rw [coe_mul_diagonal_mul]
    simp_rw [e2] at this
    rw [mul_comm ‖φ₂ _‖]
    calc _ ≤ D * ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) ^ (-N) := this
      _ = D * (t : ℝ) ^ N := by
          rw [hti, Real.inv_rpow ht0.le, Real.rpow_neg ht0.le, inv_inv]
  · have h1 : 1 ≤ (t : ℝ) := not_lt.1 ht
    rw [mul_comm ‖φ₂ _‖]
    calc _ ≤ ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ *
          ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φh (((centralSection K n t⁻¹ *
            (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
                ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ :=
          mul_le_mul_of_nonneg_left hGL.2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂ := hb
      _ ≤ C₂ * (t : ℝ) ^ max M₂ 0 := by
          rw [hti, inv_inv, max_eq_right h1]
          exact mul_le_mul_of_nonneg_left (rpow_le_of_one_lt h1) hC₂0

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

local notation "Γ₁" => rationalGLOne K n

theorem norm_thetaPairing_le {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ} (t : {r : ℝ // 0 < r}) {b : ℝ}
    (hb : ∀ x y : normOneGL K n,
      Summable (fun γ : GL (Fin n) K => ‖Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖) ∧
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ∑' γ : GL (Fin n) K, ‖Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ b) :
    ‖thetaPairing μ φ₁ φ₂ Ξ t‖ ≤ (μ (fundamentalDomain Γ₁)).toReal ^ 2 * b := by
  have hF : μ (fundamentalDomain Γ₁) < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  have hT : ∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
      φ₁ (y : AdelicGLn.AdelicGL K n) * ∑' γ : GL (Fin n) K,
        Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ b := by
    intro x y
    obtain ⟨hs, hle⟩ := hb x y
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact le_trans (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hle
  unfold thetaPairing
  have hin : ∀ x : normOneGL K n, ‖∫ y in fundamentalDomain Γ₁,
      conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        ∑' γ : GL (Fin n) K, Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) ∂μ‖ ≤
        b * (μ (fundamentalDomain Γ₁)).toReal := fun x =>
    norm_setIntegral_le_of_norm_le_const hF fun y _ => hT x y
  calc _ ≤ (b * (μ (fundamentalDomain Γ₁)).toReal) * (μ (fundamentalDomain Γ₁)).toReal :=
        norm_setIntegral_le_of_norm_le_const hF fun x _ => hin x
    _ = _ := by ring

end GJGlobal

end

end GroundTheory.Automorphic

import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.Boost

theorem vmv_mulVec {m : ℕ} (u v w : Fin m → ℂ) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem boost_exists : ∀ (m : ℕ) (ε : Fin m → Bool) (a b : Fin m → ℂ), (∀ i, ε i = false → a i = 0) → (∀ i, ε i = true → b i = 0) → ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 → ∃ A ∈ UJset ε, (∀ i, ∑ j, A i j * a j = (Real.sqrt (∑ j, ‖a j‖ ^ 2) : ℂ) * (a i + b i)) ∧ hsn A ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖a i + b i‖ ^ 2 := by
  intro m ε a b ha hb hn
  set c2 : ℝ := ∑ j, ‖a j‖ ^ 2 with hc2
  set nb : ℝ := ∑ j, ‖b j‖ ^ 2 with hnb
  have hnb0 : 0 ≤ nb := Finset.sum_nonneg fun _ _ => by positivity
  have hc1 : 1 ≤ c2 := by linarith
  have hJa : Jm ε *ᵥ a = a := by
    ext i; simp only [Jm, mulVec_diagonal]
    cases h : ε i <;> simp [ha i, h]
  have hJb : Jm ε *ᵥ b = -b := by
    ext i; simp only [Jm, mulVec_diagonal]
    cases h : ε i <;> simp [hb i, h]
  have hJa' : ∀ w, star a ⬝ᵥ (Jm ε *ᵥ w) = star a ⬝ᵥ w := by
    intro w; simp only [Jm, mulVec_diagonal, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i <;> simp [ha i, h]
  have hJb' : ∀ w, star b ⬝ᵥ (Jm ε *ᵥ w) = -(star b ⬝ᵥ w) := by
    intro w; simp only [Jm, mulVec_diagonal, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i <;> simp [hb i, h]
  have haa : star a ⬝ᵥ a = (c2 : ℂ) := by
    simp only [dotProduct, hc2, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
    push_cast; rfl
  have hbb : star b ⬝ᵥ b = (c2 : ℂ) - 1 := by
    have : star b ⬝ᵥ b = (nb : ℂ) := by
      simp only [dotProduct, hnb, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
      push_cast; rfl
    rw [this, hn]; push_cast; ring
  have hab : star a ⬝ᵥ b = 0 := by
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    cases h : ε i <;> simp [ha i, hb i, h]
  have hba : star b ⬝ᵥ a = 0 := by
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    cases h : ε i <;> simp [ha i, hb i, h]

  set s : ℝ := Real.sqrt c2 with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hc1
  have hss : s ^ 2 = c2 := Real.sq_sqrt (by linarith)
  set S : ℂ := (s : ℂ) with hS
  have hS0 : S ≠ 0 := by rw [hS]; exact_mod_cast (by linarith : s ≠ 0)
  have hS1 : S + 1 ≠ 0 := by rw [hS]; exact_mod_cast (by linarith : s + 1 ≠ 0)
  have hSS : S ^ 2 = (c2 : ℂ) := by rw [hS]; exact_mod_cast hss
  set α : ℂ := (S - 1) / S ^ 2 with hα
  set β : ℂ := 1 / (S + 1) with hβ
  set γ : ℂ := 1 / S with hγ
  have hsα : star α = α := by simp [hα, hS, Complex.conj_ofReal]
  have hsβ : star β = β := by simp [hβ, hS, Complex.conj_ofReal]
  have hsγ : star γ = γ := by simp [hγ, hS, Complex.conj_ofReal]
  set A : Matrix (Fin m) (Fin m) ℂ := 1 + α • vecMulVec a (star a) + β • vecMulVec b (star b) + γ • (vecMulVec b (star a) + vecMulVec a (star b)) with hA
  have hmul : ∀ w, A *ᵥ w = w + (α * (star a ⬝ᵥ w) + γ * (star b ⬝ᵥ w)) • a + (β * (star b ⬝ᵥ w) + γ * (star a ⬝ᵥ w)) • b := by
    intro w
    simp only [hA, add_mulVec, smul_mulVec, one_mulVec, vmv_mulVec]
    module
  have hherm : Aᴴ = A := by
    simp only [hA, conjTranspose_add, conjTranspose_smul, conjTranspose_one, conjTranspose_vecMulVec, star_star, hsα, hsβ, hsγ]
    rw [add_comm (vecMulVec a (star b))]
  have hU : A ∈ UJset ε := by
    show Aᴴ * Jm ε * A = Jm ε
    rw [hherm, Matrix.ext_iff_mulVec]
    intro v
    rw [← mulVec_mulVec, ← mulVec_mulVec, hmul, hmul]
    simp only [mulVec_add, mulVec_smul, hJa, hJb, dotProduct_add, dotProduct_smul, dotProduct_neg, hJa', hJb', haa, hbb, hab, hba, smul_eq_mul]
    set p := star a ⬝ᵥ v
    set q := star b ⬝ᵥ v
    have hX : α * p + γ * q + α * (p + (α * p + γ * q) * (c2 : ℂ)) + γ * (-q - (β * q + γ * p) * ((c2 : ℂ) - 1)) = 0 := by
      rw [hα, hβ, hγ, ← hSS]; field_simp; ring
    have hY : -(β * q + γ * p) + β * (-q - (β * q + γ * p) * ((c2 : ℂ) - 1)) + γ * (p + (α * p + γ * q) * (c2 : ℂ)) = 0 := by
      rw [hα, hβ, hγ, ← hSS]; field_simp; ring
    linear_combination (norm := module) hX • a + hY • b

  have hAa : A *ᵥ a = S • (a + b) := by
    rw [hmul, haa, hba]
    have e1 : α * (c2 : ℂ) + 1 = S := by rw [hα, ← hSS]; field_simp; try ring
    have e2 : γ * (c2 : ℂ) = S := by rw [hγ, ← hSS]; field_simp; try ring
    linear_combination (norm := module) e1 • a + e2 • b
  have hsq : A * A = 1 + (2 * α + α ^ 2 * (c2 : ℂ) + γ ^ 2 * ((c2 : ℂ) - 1)) • vecMulVec a (star a)
      + (2 * β + β ^ 2 * ((c2 : ℂ) - 1) + γ ^ 2 * (c2 : ℂ)) • vecMulVec b (star b)
      + (2 * γ + α * γ * (c2 : ℂ) + γ * β * ((c2 : ℂ) - 1)) • (vecMulVec a (star b) + vecMulVec b (star a)) := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← mulVec_mulVec, hmul, hmul]
    simp only [add_mulVec, smul_mulVec, one_mulVec, vmv_mulVec, dotProduct_add, dotProduct_smul, haa, hbb, hab, hba, smul_eq_mul]
    module
  have htr : trace (A * A) = (m : ℂ) + 4 * (c2 : ℂ) - 4 := by
    have e1 : a ⬝ᵥ star a = (c2 : ℂ) := by rw [dotProduct_comm]; exact haa
    have e2 : b ⬝ᵥ star b = (c2 : ℂ) - 1 := by rw [dotProduct_comm]; exact hbb
    have e3 : a ⬝ᵥ star b = 0 := by rw [dotProduct_comm]; exact hba
    have e4 : b ⬝ᵥ star a = 0 := by rw [dotProduct_comm]; exact hab
    rw [hsq]
    simp only [trace_add, trace_smul, trace_one, trace_vecMulVec, Fintype.card_fin, smul_eq_mul, e1, e2, e3, e4]
    rw [hα, hβ, hγ, ← hSS]; field_simp; try ring
  have hT : ∑ i, ∑ j, ‖A i j‖ ^ 2 = (m : ℝ) + 4 * c2 - 4 := by
    have : ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = trace (A * A) := by
      push_cast
      simp only [trace, Matrix.diag, mul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← Complex.mul_conj']
      congr 1
      have := congrFun (congrFun hherm j) i
      rw [conjTranspose_apply] at this
      show _ = A j i
      exact this
    rw [htr] at this
    exact_mod_cast this
  have hab2 : ∑ i, ‖a i + b i‖ ^ 2 = c2 + nb := by
    rw [hc2, hnb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i <;> simp [ha i, hb i, h]
  refine ⟨A, hU, fun i => ?_, ?_⟩
  · have := congrFun hAa i
    rw [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    exact this
  · have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    unfold hsn
    rw [Real.sq_sqrt h0, hT, hab2]
    linarith

end GlobalTheory.Boost

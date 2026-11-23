import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.YInv
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YjInv

variable {k r j : ℕ}

theorem N_ej (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) (a : Fin j) :
    n *ᵥ bvec (eI k r (Fin.castLE hj a)) =
      ∑ b : Fin j, n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a)) • bvec (eI k r (Fin.castLE hj b)) := by
  rw [N_e hn]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hj) ((Fin.castLE_injective hj).injOn) (by simp) ?_ (by simp)
  intro b _ hb
  have hb' : j ≤ b.val := by
    by_contra h
    exact hb ⟨⟨b.val, by omega⟩, by simp, rfl⟩
  have ha := a.isLt
  rw [hn.2.1 (Fin.castLE hj a) _ (by simp [eI]; omega), if_neg, zero_smul]
  intro h
  have := congrArg Fin.val h
  simp [eI] at this
  omega

theorem N_detj (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) :
    (Matrix.of fun b a : Fin j => n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a))).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) _ le_rfl, if_pos rfl]
  · intro b a hab
    have hab' : a.val < b.val := hab
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) (eI k r (Fin.castLE hj b)) hab'.le, if_neg]
    intro h
    have := congrArg Fin.val h
    simp [eI] at this
    omega

theorem Yj_N (hj : j ≤ r) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (γ : Mat k r)
    {n₁ n₂ : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (x : Mat k r) :
    Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x) := by
  have h₁' := (nSubgroup k r).2.2 _ h₁
  unfold Yj Dj
  rw [dInv k r z z' hz hz' n₁ (N_sub_S z h₁) n₂ (N_sub_S z' h₂), Ppos_N hz hz' h₁ h₂,
    ← gramProj_comb _ (fun a : Fin j => (n₂ * x)⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) _ (N_detj hj h₁')]
  congr 2
  funext a
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    N_ej hj h₁']
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.of_apply, ← Matrix.mulVec_mulVec]

theorem Yj_K (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) {κ : Mat k r} (hG : κ ∈ GG k r)
    (hκ : κ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) :
    Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x := by
  have h1 : star κ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ
  have h2 : κ * star κ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ
  have hG' : star κ * Hpk k r * κ = Hpk k r := hG
  have hc : (Hpk k r - 1) * κ = κ * (Hpk k r - 1) := by
    have : κ * Hpk k r = Hpk k r * κ := by
      conv_lhs => rw [← hG', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.mul_sub, this, Matrix.one_mul, Matrix.mul_one]
  unfold Yj
  rw [gramProj_unitary (Ppos k r z z' γ x) (Ppos k r z z' γ (x * κ)) _ κ hκ]
  · congr 2
    funext a
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ κ,
      Matrix.mul_nonsing_inv _ (det_unit hG), Matrix.one_mulVec]
  · intro p
    rw [mem_Ppos, mem_Ppos]
    simp only [Matrix.mulVec_mulVec, hc]
    refine and_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
    · rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    · have := congrArg (star κ *ᵥ ·) h
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [← Matrix.mul_assoc, h1, Matrix.one_mul] at this

theorem yj_invariant : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x) ∧ (∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x)) ∧ ∀ ρ ∈ Rset k r γ, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x := by
  intro k r j hj z z' γ hz hz' hγ x _
  refine ⟨fun κ hκ => Yj_K hj z z' γ x hκ.1 hκ.2, fun n₁ h₁ n₂ h₂ => Yj_N hj hz hz' γ h₁ h₂ x, fun ρ hρ => ?_⟩
  rw [← Yj_N hj hz hz' γ ((nSubgroup k r).2.2 _ hρ.2) hρ.1 x]
  congr 1
  have hm : IsUnit (γ * ρ * γ⁻¹).det := det_unit hρ.2.1
  have e : γ * ρ = γ * ρ * γ⁻¹ * γ := by
    rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul _ (det_unit hγ), Matrix.mul_one]
  rw [Matrix.mul_assoc]
  conv_lhs => rw [show (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ) = (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ * γ⁻¹ * γ) from by rw [← e]]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hm, Matrix.one_mul]

end GlobalTheory.Amp.YjInv

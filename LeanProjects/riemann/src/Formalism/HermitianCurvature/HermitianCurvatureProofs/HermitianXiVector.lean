import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace HermitianXiVector

open C2x5 FlagSpanVanishing

variable {k r : ℕ}

lemma herm_add_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b w : Fin n → ℂ) :
    herm H (a + b) w = herm H a w + herm H b w := by
  simp only [herm, mulVec_add, dotProduct_add]

lemma herm_smul_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (a w : Fin n → ℂ) :
    herm H (s • a) w = s * herm H a w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma herm_add_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v a b : Fin n → ℂ) :
    herm H v (a + b) = herm H v a + herm H v b := by
  simp only [herm, star_add, add_dotProduct]

lemma herm_smul_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (v a : Fin n → ℂ) :
    herm H v (s • a) = conj s * herm H v a := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
  try rfl

lemma herm_neg_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a w : Fin n → ℂ) :
    herm H (-a) w = -herm H a w := by
  simp only [herm, mulVec_neg, dotProduct_neg]

lemma herm_X_left (v u : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0)
    (hu : ∀ i : Fin (2 * r + k + 1), r + k < i.val → u i = 0) : herm (Hpk k r) v u = 0 := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : r + k < i.val
  · rw [hu i hi, star_zero, zero_mul]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    by_cases hj : r ≤ j.val
    · rw [hv j hj, mul_zero]
    · rw [show Hpk k r i j = 0 by
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega), zero_mul]

lemma herm_X_right (v u : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0)
    (hu : ∀ i : Fin (2 * r + k + 1), r + k < i.val → u i = 0) : herm (Hpk k r) u v = 0 := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : r ≤ i.val
  · rw [hv i hi, star_zero, zero_mul]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    by_cases hj : r + k < j.val
    · rw [hu j hj, mul_zero]
    · rw [show Hpk k r i j = 0 by
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega), zero_mul]

lemma xiV_X (ξ : Fin r → ℂ) : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → C2.xiV k r ξ i = 0 := by
  intro i hi
  unfold C2.xiV
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

lemma xiV_apply_last_block_zero (ξ : Fin r → ℂ) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → C2.xiV k r ξ i = 0 := by
  intro i hi
  unfold C2.xiV
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

lemma vmv_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (a b y : Fin n → ℂ) :
    vecMulVec a (star (H *ᵥ b)) *ᵥ y = herm H y b • a := by
  have hH' : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    rwa [conjTranspose_apply] at this
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, herm, Pi.star_apply, star_sum, star_mul', hH', Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

private lemma hpk_conjTranspose_self (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | (simp; done) | (exfalso; omega)

lemma nEich_apply (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    C2.nEich k r z ξ *ᵥ y = y + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • (-(herm (Hpk k r) y z) • C2.xiV k r ξ +
      herm (Hpk k r) y (C2.xiV k r ξ) • z + ((1 / 2 : ℂ) * herm (Hpk k r) y (C2.xiV k r ξ)) • C2.xiV k r ξ) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := hpk_conjTranspose_self k r
  first
  | simp only [C2.nEich, add_mulVec, one_mulVec, smul_mulVec, neg_mulVec, vmv_apply _ hH, neg_smul, smul_smul]
  | simp only [C2.nEich, add_mulVec, one_mulVec, Matrix.smul_mulVec_assoc, neg_mulVec, vmv_apply _ hH, neg_smul, smul_smul]

end HermitianXiVector

namespace HermitianXiVector

open C2x5 FlagSpanVanishing

variable {k r : ℕ}

lemma herm_neg_r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v a : Fin n → ℂ) :
    herm H v (-a) = -herm H v a := by
  simp only [herm, star_neg, neg_dotProduct]

lemma herm_basis {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    herm H (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single i 1) = (Aᴴ * H * A) i j := by
  have e1 : herm H (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single i 1) =
      herm (Aᴴ * H * A) (Pi.single j 1) (Pi.single i 1) := by
    simp only [herm, star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]
  rw [e1]
  simp [herm, dotProduct, mulVec, Pi.single_apply]

lemma uh_of_herm {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ y y', herm H (A *ᵥ y) (A *ᵥ y') = herm H y y') : A ∈ UH H := by
  show Aᴴ * H * A = H
  ext i j
  have h1 := h (Pi.single j 1) (Pi.single i 1)
  rw [herm_basis] at h1
  rw [h1]
  simp [herm, dotProduct, mulVec, Pi.single_apply]

lemma nEich_herm {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) (y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (C2.nEich k r z ξ *ᵥ y) (C2.nEich k r z ξ *ᵥ y') = herm (Hpk k r) y y' := by
  have hH := GBasic.Hpk_herm k r
  have hxx : herm (Hpk k r) (C2.xiV k r ξ) (C2.xiV k r ξ) = 0 :=
    herm_X_left _ _ (xiV_X ξ) (xiV_apply_last_block_zero ξ)
  have hxz : herm (Hpk k r) (C2.xiV k r ξ) z = 0 :=
    herm_X_left _ z (xiV_X ξ) (fun i hi => hz.1 i (Or.inr hi))
  have hzx : herm (Hpk k r) z (C2.xiV k r ξ) = 0 :=
    herm_X_right _ z (xiV_X ξ) (fun i hi => hz.1 i (Or.inr hi))
  have hzz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by rw [hzz_real]; push_cast; ring
  have hxy : herm (Hpk k r) (C2.xiV k r ξ) y' = conj (herm (Hpk k r) y' (C2.xiV k r ξ)) := ggHerm_swap _ hH _ _
  have hzy : herm (Hpk k r) z y' = conj (herm (Hpk k r) y' z) := ggHerm_swap _ hH _ _
  have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz.2.ne'
  have hcc : conj ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := by
    rw [map_div₀, map_one, Complex.conj_ofReal]
  rw [nEich_apply, nEich_apply]
  simp only [herm_add_l, herm_add_r, herm_smul_l, herm_smul_r, herm_neg_l, herm_neg_r, hxx, hxz, hzx, hzz,
    hxy, hzy, hcc, map_neg, map_mul, map_div₀, map_one, map_ofNat]
  set c : ℂ := (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) with hc
  have hcT : c * ((Tz k r z : ℝ) : ℂ) = 1 := by rw [hc]; field_simp
  linear_combination (-(c * herm (Hpk k r) y (C2.xiV k r ξ) * conj (herm (Hpk k r) y' (C2.xiV k r ξ)))) * hcT

lemma nEich_col {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) :
    WeylGroupFacts.col k r (C2.nEich k r z ξ) := by
  intro i j hj hij
  have e : (C2.nEich k r z ξ *ᵥ bvec j) i = C2.nEich k r z ξ i j := by rw [mulVec_bvec]
  rw [← e, nEich_apply]
  have hjx : herm (Hpk k r) (bvec j) (C2.xiV k r ξ) = 0 :=
    herm_X_right (C2.xiV k r ξ) (bvec j) (xiV_X ξ) (fun p hp => by
      simp only [bvec, Pi.single_apply]; rw [if_neg (fun e => by rw [e] at hp; omega)])
  rw [hjx]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, Pi.neg_apply, zero_mul, mul_zero,
    add_zero]
  by_cases hir : r ≤ i.val
  · rw [xiV_X ξ i hir]; simp
  · have hjr : j.val < r := by omega
    have hjz : herm (Hpk k r) (Pi.single j 1) z = 0 :=
      herm_X_left (Pi.single j 1) z (fun p hp => by
        simp only [Pi.single_apply]; rw [if_neg (fun e => by rw [e] at hp; omega)])
        (fun p hp => hz.1 p (Or.inr hp))
    rw [hjz]; simp

lemma nEich_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) :
    C2.nEich k r z ξ ∈ Nset k r := by
  rw [WeylGroupFacts.nset_iff]
  exact ⟨uh_of_herm _ _ (nEich_herm hz ξ), nEich_col hz ξ⟩

end HermitianXiVector

end Formalism.FourierDecayAlt.P

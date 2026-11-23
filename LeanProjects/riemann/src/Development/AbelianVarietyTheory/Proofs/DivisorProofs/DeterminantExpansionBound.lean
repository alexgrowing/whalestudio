import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix GlobalTheory.HermFrame
open scoped ComplexOrder ComplexConjugate

namespace GlobalTheory.MixedDiscriminant

variable {n : ℕ}

theorem alt_sum_eq_det (N : Matrix (Fin n) (Fin n) ℂ) (p : Equiv.Perm (Fin n)) :
    ∑ t : Equiv.Perm (Fin n), ((Equiv.Perm.sign t : ℤ) : ℂ) * ∏ k, N (t (p k)) k =
      (N.submatrix id p.symm).det := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Equiv.prod_comp p (fun i => N.submatrix id p.symm (t i) i)]
  simp

theorem alt_sum_change (N R Q : Matrix (Fin n) (Fin n) ℂ) (p : Equiv.Perm (Fin n))
    (h : ∀ i k, N i k = ∑ a, Q a i * R a k) :
    ∑ t : Equiv.Perm (Fin n), ((Equiv.Perm.sign t : ℤ) : ℂ) * ∏ k, N (t (p k)) k =
      Q.det * ∑ t : Equiv.Perm (Fin n), ((Equiv.Perm.sign t : ℤ) : ℂ) * ∏ k, R (t (p k)) k := by
  rw [alt_sum_eq_det, alt_sum_eq_det, ← det_transpose Q, ← det_mul]
  congr 1
  ext i k
  simp [h, mul_apply]

theorem eq_sum_single (v : Fin n → ℂ) : v = ∑ a, v a • (Pi.single a 1 : Fin n → ℂ) := by
  ext b; simp [Pi.single_apply]

theorem sesq_left {F : (Fin n → ℂ) → (Fin n → ℂ) → ℂ} (hF : IsSesq F) (v w : Fin n → ℂ) :
    F v w = ∑ a, v a * F (Pi.single a 1) w := by
  let L : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => F x w
      map_add' := fun x y => hF.add_left x y w
      map_smul' := fun c x => hF.smul_left c x w }
  change L v = ∑ a, v a * L (Pi.single a 1)
  conv_lhs => rw [eq_sum_single v, map_sum]
  simp

theorem sesq_right {F : (Fin n → ℂ) → (Fin n → ℂ) → ℂ} (hF : IsSesq F) (v w : Fin n → ℂ) :
    F v w = ∑ a, conj (w a) * F v (Pi.single a 1) := by
  let L : (Fin n → ℂ) →ₛₗ[starRingEnd ℂ] ℂ :=
    { toFun := fun x => F v x
      map_add' := fun x y => hF.add_right v x y
      map_smul' := fun c x => hF.smul_right c v x }
  change L w = ∑ a, conj (w a) * L (Pi.single a 1)
  conv_lhs => rw [eq_sum_single w, map_sum]
  simp [map_smulₛₗ]

noncomputable def dsum {J : Type} [Fintype J] (π : J → Equiv.Perm (Fin n))
    (c : J → Fin n → Fin n → Fin n → ℂ) : ℂ :=
  ∑ s : Equiv.Perm (Fin n), ∑ t : Equiv.Perm (Fin n),
    (((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) : ℂ) * ∑ j, ∏ k, c j k (s k) (t (π j k))

theorem dsum_left {J : Type} [Fintype J] (π : J → Equiv.Perm (Fin n))
    (c d : J → Fin n → Fin n → Fin n → ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ j k i b, c j k i b = ∑ a, Q a i * d j k a b) : dsum π c = Q.det * dsum π d := by
  have e : ∀ c : J → Fin n → Fin n → Fin n → ℂ, dsum π c =
      ∑ t : Equiv.Perm (Fin n), ∑ j, ((Equiv.Perm.sign t : ℤ) : ℂ) *
        ∑ s : Equiv.Perm (Fin n), ((Equiv.Perm.sign s : ℤ) : ℂ) *
          ∏ k, c j k (s ((1 : Equiv.Perm (Fin n)) k)) (t (π j k)) := by
    intro c
    rw [dsum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [Units.val_mul, Int.cast_mul, Equiv.Perm.one_apply]; ring
  rw [e, e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := alt_sum_change (of fun i k => c j k i (t (π j k))) (of fun i k => d j k i (t (π j k)))
    Q 1 (fun i k => h j k i _)
  simp only [of_apply] at this
  rw [this]; ring

theorem dsum_right {J : Type} [Fintype J] (π : J → Equiv.Perm (Fin n))
    (c d : J → Fin n → Fin n → Fin n → ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ j k b i, c j k b i = ∑ a, Q a i * d j k b a) : dsum π c = Q.det * dsum π d := by
  have e : ∀ c : J → Fin n → Fin n → Fin n → ℂ, dsum π c =
      ∑ s : Equiv.Perm (Fin n), ∑ j, ((Equiv.Perm.sign s : ℤ) : ℂ) *
        ∑ t : Equiv.Perm (Fin n), ((Equiv.Perm.sign t : ℤ) : ℂ) *
          ∏ k, c j k (s k) (t (π j k)) := by
    intro c
    rw [dsum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
    simp only [Units.val_mul, Int.cast_mul]; ring
  rw [e, e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := alt_sum_change (of fun i k => c j k (s k) i) (of fun i k => d j k (s k) i)
    Q (π j) (fun i k => h j k _ i)
  simp only [of_apply] at this
  rw [this]; ring

theorem exists_basis {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosSemidef) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, ‖P.det‖ = 1 ∧
      ∏ i, gnorm G (fun a => P a i) ^ 2 = G.det.re := by
  have hT := hG.transpose
  refine ⟨hT.isHermitian.eigenvectorUnitary, ?_, ?_⟩
  · exact CStarRing.norm_of_mem_unitary (det_of_mem_unitary hT.isHermitian.eigenvectorUnitary.2)
  · rw [← det_transpose G, hT.isHermitian.det_eq_prod_eigenvalues]
    have : ∀ i, gnorm G (fun a => (hT.isHermitian.eigenvectorUnitary : Matrix _ _ ℂ) a i) ^ 2 =
        hT.isHermitian.eigenvalues i := by
      intro i
      rw [gnorm_sq hG, form_eq_transpose, hT.isHermitian.eigenvalues_eq]
      rfl
    simp only [this]
    change _ = (∏ i, ((hT.isHermitian.eigenvalues i : ℝ) : ℂ)).re
    rw [← Complex.ofReal_prod, Complex.ofReal_re]

theorem norm_double_alt_sum_le (n : ℕ) (J : Type) [Fintype J]
    (f : J → Fin n → (Fin n → ℂ) → (Fin n → ℂ) → ℂ) (π : J → Equiv.Perm (Fin n))
    (G : Matrix (Fin n) (Fin n) ℂ) (K : ℝ) (hf : ∀ j k, IsSesq (f j k)) (hG : G.PosSemidef)
    (hK : ∀ x y : Fin n → Fin n → ℂ, ‖∑ j, ∏ k, f j k (x k) (y (π j k))‖ ≤
      K * ∏ k, (gnorm G (x k) * gnorm G (y k))) :
    ‖∑ s : Equiv.Perm (Fin n), ∑ t : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) : ℂ) *
        ∑ j, ∏ k, f j k (Pi.single (s k) 1) (Pi.single (t (π j k)) 1)‖ ≤
      (n.factorial : ℝ) ^ 2 * K * G.det.re := by
  obtain ⟨P, hP, hd⟩ := exists_basis hG
  let u : Fin n → Fin n → ℂ := fun i a => P a i
  have h1 := dsum_left π (fun j k a b => f j k (u a) (u b))
    (fun j k a b => f j k (Pi.single a 1) (u b)) P (fun j k i b => sesq_left (hf j k) _ _)
  have h2 := dsum_right π (fun j k a b => f j k (Pi.single a 1) (u b))
    (fun j k a b => f j k (Pi.single a 1) (Pi.single b 1)) (P.map (starRingEnd ℂ))
    (fun j k i b => sesq_right (hf j k) _ _)
  have h3 : ‖(P.map (starRingEnd ℂ)).det‖ = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.norm_conj, hP]
  have h4 : ‖dsum π (fun j k a b => f j k (Pi.single a 1) (Pi.single b 1))‖ =
      ‖dsum π (fun j k a b => f j k (u a) (u b))‖ := by
    rw [h1, h2, norm_mul, norm_mul, hP, h3, one_mul, one_mul]
  refine h4.le.trans ?_
  have h5 : ∀ s t : Equiv.Perm (Fin n),
      ‖(((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) : ℂ) *
        ∑ j, ∏ k, f j k (u (s k)) (u (t (π j k)))‖ ≤ K * G.det.re := by
    intro s t
    have hs : ‖(((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign s * Equiv.Perm.sign t) with h | h <;>
        rw [h] <;> simp
    rw [norm_mul, hs, one_mul]
    refine (hK (fun k => u (s k)) (fun k => u (t k))).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, Equiv.prod_comp s (fun k => gnorm G (u k)),
      Equiv.prod_comp t (fun k => gnorm G (u k)), ← hd, Finset.prod_pow, sq]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun s _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun t _ => h5 s t)).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  ring

end GlobalTheory.MixedDiscriminant

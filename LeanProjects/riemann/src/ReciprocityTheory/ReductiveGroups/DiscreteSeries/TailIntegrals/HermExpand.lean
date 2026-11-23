import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianFormLiftVecFirstVector

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem herm_conj {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (v w : Fin n → ℂ) :
    star (herm H v w) = herm H w v := by
  have h : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this
  unfold herm
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h]; ring

theorem dot_bvec_r {n : ℕ} (i : Fin n) (x : Fin n → ℂ) : x ⬝ᵥ bvec i = x i := by
  simp [bvec]

section ex
variable (k n : ℕ)

def wp (i : Fin (k - 1)) : Fin (2 * n + k + 1) := wI k n ⟨i.val + 1, by omega⟩

def wv (i : Fin (k - 1)) : Fin (2 * n + k + 1) → ℂ := bvec (wp k n i)

theorem wp_val (i : Fin (k - 1)) : (wp k n i).val = n + (i.val + 1) := rfl

theorem sg_wp (i : Fin (k - 1)) : sg k n (wp k n i).val = (wp k n i).val := by
  have hi := i.isLt
  rw [wp_val]
  unfold sg
  rw [if_neg (by omega)]

private theorem Hpk_apply_wp_eq_ite (i : Fin (k - 1)) (j : Fin (2 * n + k + 1)) :
    Hpk k n (wp k n i) j = if wp k n i = j then 1 else 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have hj := j.isLt
  have hij : wp k n i = j ↔ (wp k n i).val = j.val := Fin.ext_iff
  unfold Hpk
  by_cases h : (wp k n i).val = j.val
  · rw [if_pos (hij.2 h), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, hij.2 h⟩,
      if_neg (by omega)]
  · rw [if_neg (fun he => h (hij.1 he)), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem hpk_mv_w (i : Fin (k - 1)) (y : Fin (2 * n + k + 1) → ℂ) : (Hpk k n *ᵥ y) (wp k n i) = y (wp k n i) := by
  simp only [mulVec, dotProduct, Hpk_apply_wp_eq_ite, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem hpk_bvec_w (i : Fin (k - 1)) : Hpk k n *ᵥ wv k n i = wv k n i := by
  funext p
  have hc : Hpk k n p (wp k n i) = star (Hpk k n (wp k n i) p) := by
    have := congrFun (congrFun (hpk_conjT k n) p) (wp k n i)
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  simp only [wv, bvec, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hc, Hpk_apply_wp_eq_ite]
  by_cases h : wp k n i = p
  · subst h; simp
  · rw [if_neg h, if_neg (fun he => h he.symm), star_zero]

theorem phi_w (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV k n a (wp k n i) = 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have ha := a.isLt
  unfold phiV
  split_ifs with h
  · simp only [bvec]
    rw [Pi.single_apply, if_neg]
    intro he
    have := congrArg Fin.val he
    simp only [esI] at this
    omega
  · simp only [epsV, bvec, Pi.smul_apply, Pi.add_apply, Pi.single_apply]
    rw [if_neg, if_neg]
    · simp
    · intro he
      have := congrArg Fin.val he
      simp [wI, Fin.val_last] at this <;> omega
    · intro he
      have := congrArg Fin.val he
      simp [wI] at this <;> omega

theorem phi'_w (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV' k n a (wp k n i) = 0 := by
  show (Hpk k n *ᵥ phiV k n a) (wp k n i) = 0
  rw [hpk_mv_w, phi_w]

theorem herm_w_l (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) (wv k n i) v = star (v (wp k n i)) := by
  unfold herm
  rw [hpk_bvec_w]
  simp only [wv]
  rw [dot_bvec_r]
  rfl

theorem herm_w_r (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) v (wv k n i) = v (wp k n i) := by
  unfold herm
  have hs : star (wv k n i) = Pi.single (wp k n i) (1 : ℂ) := by
    ext j
    by_cases h : j = wp k n i <;> simp [wv, bvec, h]
  rw [hs, single_dotProduct, one_mul, hpk_mv_w]

def Phv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV' k n) (Sum.elim (phiV k n) (wv k n))

def Psv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV k n) (Sum.elim (phiV' k n) (wv k n))

private theorem herm_Hpk_mulVec_Hpk_mulVec (x y : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) (Hpk k n *ᵥ x) (Hpk k n *ᵥ y) = herm (Hpk k n) x y := by
  unfold herm
  rw [mulVec_mulVec, hpk_mul, one_mulVec, Matrix.star_mulVec, hpk_conjT, dotProduct_mulVec]

theorem pair_all (hk : 1 ≤ k) (c d : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1))) :
    herm (Hpk k n) (Phv k n d) (Psv k n c) = if c = d then 1 else 0 := by
  have hφ' : ∀ a, phiV' k n a = Hpk k n *ᵥ phiV k n a := fun _ => rfl
  rcases c with b | b | i <;> rcases d with a | a | j <;>
    simp only [Phv, Psv, Sum.elim_inl, Sum.elim_inr]
  · rw [← herm_conj (Hpk k n) (hpk_conjT k n) (phiV k n b) (phiV' k n a), phi_pair k n hk]
    by_cases h : b = a
    · subst h; simp
    · simp [h]
  · rw [phi_iso k n hk]; simp
  · rw [herm_w_l, phi_w]; simp
  · rw [hφ', hφ', herm_Hpk_mulVec_Hpk_mulVec, phi_iso k n hk]; simp
  · rw [phi_pair k n hk]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [herm_w_l, phi'_w]; simp
  · rw [herm_w_r, phi'_w]; simp
  · rw [herm_w_r, phi_w]; simp
  · rw [herm_w_l]
    simp only [wv, bvec, Pi.single_apply]
    by_cases h : i = j
    · subst h; simp
    · have hne : wp k n j ≠ wp k n i := by
        intro he
        apply h
        ext
        have := congrArg Fin.val he
        rw [wp_val, wp_val] at this
        omega
      simp [hne, h]

private theorem herm_sum_smul_left_tail_integrals {ι : Type*} [Fintype ι] (g : ι → ℂ) (v : ι → Fin (2 * n + k + 1) → ℂ)
    (w : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) (∑ c, g c • v c) w = ∑ c, g c * herm (Hpk k n) (v c) w := by
  unfold herm
  simp only [dotProduct, mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem expand (hk : 1 ≤ k) (y : Fin (2 * n + k + 1) → ℂ) :
    y = ∑ c, herm (Hpk k n) y (Psv k n c) • Phv k n c := by
  have hcoef : ∀ (g : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → ℂ) c,
      herm (Hpk k n) (∑ d, g d • Phv k n d) (Psv k n c) = g c := by
    intro g c
    rw [herm_sum_smul_left_tail_integrals]
    simp [pair_all k n hk]
  have hli : LinearIndependent ℂ (Phv k n) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c
    have := hcoef g c
    rw [hg] at this
    simpa [herm] using this.symm
  have hcard : Fintype.card (Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1))) =
      Module.finrank ℂ (Fin (2 * n + k + 1) → ℂ) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Module.finrank_fin_fun]
    omega
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ c, b c = Phv k n c := fun c => by simp [b]
  have hy := b.sum_repr y
  simp only [hb] at hy
  conv_lhs => rw [← hy]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hcoef (fun d => b.repr y d) c
  rw [hy] at this
  rw [this]

theorem herm_expand (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) y w = ∑ j, (herm (Hpk k n) y (phiV k n j) * herm (Hpk k n) (phiV' k n j) w +
      herm (Hpk k n) y (phiV' k n j) * herm (Hpk k n) (phiV k n j) w) +
      ∑ i, y (wp k n i) * herm (Hpk k n) (wv k n i) w := by
  conv_lhs => rw [expand k n hk y]
  rw [herm_sum_smul_left_tail_integrals, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Psv, Phv, Sum.elim_inl, Sum.elim_inr, herm_w_r]
  rw [Finset.sum_add_distrib]
  exact (add_assoc _ _ _).symm

theorem herm_linF (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (fun j => herm (Hpk k n) (phiV' k n (Fin.cast (by omega) j)) w)
      (fun j => herm (Hpk k n) (phiV k n (Fin.cast (by omega) j)) w) (fun i => herm (Hpk k n) (wv k n i) w)
      (hcoord k n (y, s)) := by
  rw [herm_expand k n hk y w]
  simp only [linF, hcoord]
  congr 1
  exact ((finCongr (by omega : 1 + n = n + 1)).sum_comp (fun j =>
    herm (Hpk k n) y (phiV k n j) * herm (Hpk k n) (phiV' k n j) w +
      herm (Hpk k n) y (phiV' k n j) * herm (Hpk k n) (phiV k n j) w)).symm

end ex

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi

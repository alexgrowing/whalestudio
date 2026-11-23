import Mathlib
import Formalism.BranchSandwichDivisors.StatementW
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockbLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL

noncomputable section

namespace Formalism.BranchingDeterminantCap

section XiA

variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

lemma xn_det_supported {σ m : Type*} [Fintype m] [DecidableEq m] (s : Set σ)
    (A : Matrix m m (MvPolynomial σ ℂ)) (h : ∀ i j, A i j ∈ supported ℂ s) :
    A.det ∈ supported ℂ s := by
  rw [Matrix.det_apply']
  refine sum_mem fun τ _ => mul_mem ?_ (prod_mem fun i _ => h _ _)
  first
  | exact intCast_mem _ _
  | exact Subalgebra.intCast_mem _ _
  | (rw [← map_intCast (algebraMap ℂ (MvPolynomial σ ℂ))]; exact Subalgebra.algebraMap_mem _ _)

lemma xn_pderiv_supported {σ : Type*} (s : Set σ) (v : σ) (hv : v ∉ s) (f : MvPolynomial σ ℂ)
    (hf : f ∈ supported ℂ s) : pderiv v f = 0 := by
  rw [MvPolynomial.mem_supported] at hf
  first
  | exact MvPolynomial.pderiv_eq_zero_of_notMem_vars fun hv' => hv (hf hv')
  | exact MvPolynomial.pderiv_eq_zero_of_not_mem_vars fun hv' => hv (hf hv')

lemma xn_minor_zero {s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) (h : ¬ Function.Injective I) :
    initMinor ℂ I hs = 0 := by
  unfold Function.Injective at h
  push_neg at h
  obtain ⟨i, j, hij, hne⟩ := h
  unfold initMinor
  exact Matrix.det_zero_of_row_eq hne (funext fun q => by simp [hij])

def xnCof (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (j : Fin (p + 1)) :
    MvPolynomial (Fin r × Fin n) ℂ :=
  (-1) ^ (p + j.val) * (Matrix.of fun i k : Fin p =>
    (X (ι (a i), Fin.castLE hp (j.succAbove k)) : MvPolynomial (Fin r × Fin n) ℂ)).det

lemma xn_lap (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (b : κ) :
    initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp =
      ∑ j, X (ι b, Fin.castLE hp j) * xnCof ι hp a j := by
  unfold initMinor xnCof
  rw [Matrix.det_succ_row _ (Fin.last p)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Fin.snoc_last, Fin.val_last,
    Fin.succAbove_last, Fin.snoc_castSucc]
  ring

lemma xn_cof_last (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) :
    xnCof ι hp a (Fin.last p) = initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) := by
  unfold xnCof initMinor
  rw [Fin.val_last, (Even.neg_one_pow ⟨p, rfl⟩ : ((-1 : MvPolynomial (Fin r × Fin n) ℂ)) ^ (p + p) = 1),
    one_mul]
  congr 1
  refine Matrix.ext fun i k => ?_
  simp only [Matrix.of_apply, Function.comp_apply, Fin.succAbove_last]
  rfl

lemma xn_cof_supported (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (j : Fin (p + 1)) :
    xnCof ι hp a j ∈ supported ℂ {v : Fin r × Fin n | ∃ i, v.1 = ι (a i)} := by
  unfold xnCof
  refine mul_mem (pow_mem (neg_mem (one_mem _)) _) (xn_det_supported _ _ fun i k => ?_)
  rw [Matrix.of_apply]
  first
  | exact (MvPolynomial.X_mem_supported (R := ℂ)).2 ⟨i, rfl⟩
  | exact MvPolynomial.X_mem_supported.mpr ⟨i, rfl⟩

lemma xn_part1 (ι : κ → Fin r) (hι : Function.Injective ι) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (b : κ) :
    pderiv (ι b, (⟨p, hp⟩ : Fin n)) (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp) =
      if b ∈ Finset.univ.image a then 0 else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) := by
  split_ifs with hb
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hb
    have hni : ¬ Function.Injective (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) := by
      intro hinj
      have h2 := @hinj (Fin.castSucc i) (Fin.last p) (by simp [hi])
      exact (Fin.castSucc_lt_last i).ne h2
    rw [xn_minor_zero _ hp hni, map_zero]
  · have hns : ((ι b, (⟨p, hp⟩ : Fin n)) : Fin r × Fin n) ∉
        {v : Fin r × Fin n | ∃ i, v.1 = ι (a i)} := by
      rintro ⟨i, hi⟩
      exact hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, (hι hi).symm⟩)
    rw [xn_lap ι hp a b, map_sum, Finset.sum_eq_single (Fin.last p), ← xn_cof_last ι hp a]
    · rw [Derivation.leibniz, xn_pderiv_supported _ _ hns _ (xn_cof_supported ι hp a _), smul_zero,
        zero_add, MvPolynomial.pderiv_X, smul_eq_mul]
      simp [Pi.single_apply, Fin.ext_iff]
    · intro j _ hj
      have hjv : (j : ℕ) ≠ p := fun h => hj (Fin.ext (by simpa using h))
      rw [Derivation.leibniz, xn_pderiv_supported _ _ hns _ (xn_cof_supported ι hp a _), smul_zero,
        zero_add, MvPolynomial.pderiv_X, smul_eq_mul]
      simp [Pi.single_apply, Fin.ext_iff, hjv]
    · simp

lemma xn_part2 (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (m : ℂ)
    (h0 : ∀ t : Fin n, t.val < p → ∑ b : κ, X (ι b, t) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = 0)
    (h1 : ∑ b : κ, X (ι b, (⟨p, hp⟩ : Fin n)) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = C m * f) :
    ∑ b : κ, initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp *
        pderiv (ι b, (⟨p, hp⟩ : Fin n)) f =
      C m * (initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) * f) := by
  have hl : Fin.castLE hp (Fin.last p) = (⟨p, hp⟩ : Fin n) := Fin.ext (by simp)
  simp only [xn_lap ι hp a, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_eq_single (Fin.last p)]
  · simp only [hl]
    simp_rw [mul_right_comm _ (xnCof ι hp a (Fin.last p)) _]
    rw [← Finset.sum_mul, h1, xn_cof_last]
    ring
  · intro j _ hj
    have hjv : (Fin.castLE hp j).val < p := by
      have h3 : (j : ℕ) ≠ p := fun h => hj (Fin.ext (by simpa using h))
      have h4 := j.isLt
      simp only [Fin.coe_castLE]
      omega
    simp_rw [mul_right_comm _ (xnCof ι hp a j) _]
    rw [← Finset.sum_mul, h0 (Fin.castLE hp j) hjv, zero_mul]
  · simp

lemma xn_key (ι : κ → Fin r) (hι : Function.Injective ι) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (m : ℂ)
    (h0 : ∀ t : Fin n, t.val < p → ∑ b : κ, X (ι b, t) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = 0)
    (h1 : ∑ b : κ, X (ι b, (⟨p, hp⟩ : Fin n)) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = C m * f) :
    ∑ b : κ, pderiv (ι b, (⟨p, hp⟩ : Fin n))
        (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * f) =
      C ((Fintype.card κ : ℂ) - p + m) * (initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) * f) := by
  have hsplit : ∀ b : κ, pderiv (ι b, (⟨p, hp⟩ : Fin n))
      (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * f) =
      initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f +
      f * (if b ∈ Finset.univ.image a then 0 else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) := by
    intro b
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, xn_part1 ι hι hp a b]
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [xn_part2 ι hp a f m h0 h1]
  by_cases ha : Function.Injective a
  · have hsum : ∑ b : κ, (if b ∈ Finset.univ.image a then (0 : MvPolynomial (Fin r × Fin n) ℂ)
        else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) =
        ((Fintype.card κ : MvPolynomial (Fin r × Fin n) ℂ) - p) *
          initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) := by
      rw [Finset.sum_congr rfl fun b _ => (show (if b ∈ Finset.univ.image a then
          (0 : MvPolynomial (Fin r × Fin n) ℂ) else initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp)) =
          initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) - (if b ∈ Finset.univ.image a then
          initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) else 0) by split_ifs <;> simp)]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, Finset.card_image_of_injective _ ha]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsum, map_add, map_sub, map_natCast, map_natCast]
    ring
  · have hz : initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) = 0 :=
      xn_minor_zero _ _ fun h => ha h.of_comp
    simp [hz]

end XiA

section XiB

variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

def xnMono (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) : MvPolynomial (Fin r × Fin n) ℂ :=
  ∏ q : Fin p, X (ι (a q), Fin.castLE hp q)

def xnC (M : ℕ) (m : ℕ → ℕ) (p : ℕ) : ℝ := ∏ q ∈ Finset.range p, ((M : ℝ) - q + m q)

def xnSg {p : ℕ} (π : Equiv.Perm (Fin p)) : ℂ := ((Equiv.Perm.sign π : ℤ) : ℂ)

lemma xnSg_mul_self {p : ℕ} (π : Equiv.Perm (Fin p)) : xnSg π * xnSg π = 1 := by
  unfold xnSg
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

lemma xnSg_star {p : ℕ} (π : Equiv.Perm (Fin p)) : star (xnSg π) = xnSg π := by
  unfold xnSg
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

lemma xn_minor_sum (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) :
    initMinor ℂ (ι ∘ a) hp = ∑ π : Equiv.Perm (Fin p), C (xnSg π) * xnMono ι hp (a ∘ π) := by
  unfold initMinor xnMono xnSg
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_intCast]
  rfl

lemma xn_minor_perm (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) (π : Equiv.Perm (Fin p)) :
    initMinor ℂ (ι ∘ (a ∘ π)) hp = C (xnSg π) * initMinor ℂ (ι ∘ a) hp := by
  unfold initMinor xnSg
  first
  | (rw [map_intCast, ← Matrix.det_permute]; rfl)
  | (rw [map_intCast]
     exact Matrix.det_permute π (Matrix.of fun x y : Fin p =>
       (X ((ι ∘ a) x, Fin.castLE hp y) : MvPolynomial (Fin r × Fin n) ℂ)))

private lemma prod_factorial_single_add_eq_mul' (v : Fin r × Fin n) (m : (Fin r × Fin n) →₀ ℕ) :
    (∏ k ∈ (Finsupp.single v 1 + m).support,
      ((Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k).factorial) =
      (m v + 1) * ∏ k ∈ m.support, (m k).factorial := by
  set T := insert v m.support with hTdef
  have hT : ∀ u : (Fin r × Fin n) →₀ ℕ, u.support ⊆ T →
      ∏ k ∈ u.support, (u k).factorial = (u v).factorial * ∏ k ∈ T.erase v, (u k).factorial := by
    intro u hu
    rw [Finset.mul_prod_erase T (fun k => (u k).factorial) (Finset.mem_insert_self v _)]
    refine Finset.prod_subset hu fun k _ hk => ?_
    have h0 : u k = 0 := by simpa using hk
    rw [h0, Nat.factorial_zero]
  have hsub : (Finsupp.single v 1 + m).support ⊆ T := by
    intro k hk
    by_contra hc
    have hkv : k ≠ v := by
      rintro rfl
      exact hc (Finset.mem_insert_self _ _)
    have hkm : m k = 0 := by
      by_contra hm
      exact hc (Finset.mem_insert_of_mem (Finsupp.mem_support_iff.2 hm))
    have h5 : (Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k = 0 := by simp [Finsupp.single_apply, Ne.symm hkv, hkm]
    exact (Finsupp.mem_support_iff.1 hk) h5
  rw [hT _ hsub, hT m (Finset.subset_insert _ _)]
  have hrest : ∏ k ∈ T.erase v, ((Finsupp.single v 1 + m : (Fin r × Fin n) →₀ ℕ) k).factorial =
      ∏ k ∈ T.erase v, (m k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkv : k ≠ v := Finset.ne_of_mem_erase hk
    simp [Finsupp.single_apply, Ne.symm hkv]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm 1, Nat.factorial_succ]
  ring

private lemma coeff_pderiv_eq_mul_coeff_single_add (v : Fin r × Fin n) (m : (Fin r × Fin n) →₀ ℕ)
    (H : MvPolynomial (Fin r × Fin n) ℂ) :
    (pderiv v H).coeff m = ((m v + 1 : ℕ) : ℂ) * H.coeff (Finsupp.single v 1 + m) := by
  induction H using MvPolynomial.induction_on'
  next u a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hu : u = Finsupp.single v 1 + m
    · subst hu
      rw [add_tsub_cancel_left, if_pos rfl, if_pos rfl]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast
      ring
    · rw [if_neg hu, mul_zero]
      split_ifs with h2
      · have h3 : u v = 0 := by
          by_contra h4
          apply hu
          rw [← h2]
          ext k
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with h5
          · subst h5
            omega
          · omega
        rw [h3]
        simp
      · rfl
  next p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]

private lemma fockF_X_mul_eq_pderiv (v : Fin r × Fin n) (G H : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (X v * G) H = fockF G (pderiv v H) := by
  unfold fockF
  rw [MvPolynomial.support_X_mul, Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [addLeftEmbedding_apply, MvPolynomial.coeff_X_mul, coeff_pderiv_eq_mul_coeff_single_add, prod_factorial_single_add_eq_mul', star_mul']
  push_cast
  rw [show star ((m v : ℂ) + 1) = (m v : ℂ) + 1 by simp]
  ring

private lemma fockF_sum_right' {ι' : Type*} (s : Finset ι') (F : MvPolynomial (Fin r × Fin n) ℂ)
    (G : ι' → MvPolynomial (Fin r × Fin n) ℂ) :
    fockF F (∑ i ∈ s, G i) = ∑ i ∈ s, fockF F (G i) := by
  unfold fockF
  simp only [MvPolynomial.coeff_sum, star_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma fockF_C_mul_right (F G : MvPolynomial (Fin r × Fin n) ℂ) (c : ℂ) :
    fockF F (C c * G) = star c * fockF F G := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul, star_mul']
  ring

lemma fock_pairing_initial_minor (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) (g : MvPolynomial (Fin r × Fin n) ℂ) :
    ∑ a : Fin p → κ, fockF (xnMono ι hp a * g) (initMinor ℂ (ι ∘ a) hp * f) =
      ((xnC (Fintype.card κ) m p : ℝ) : ℂ) * fockF g f := by
  induction p generalizing g with
  | zero =>
    simp [xnMono, xnC, initMinor]
  | succ p ih =>
    have hp0 : p ≤ n := Nat.le_of_succ_le hp
    have hre : ∀ F : (Fin (p + 1) → κ) → ℂ,
        ∑ a, F a = ∑ a' : Fin p → κ, ∑ b : κ, F (Fin.snoc a' b : Fin (p + 1) → κ) := by
      intro F
      rw [← Fintype.sum_prod_type']
      symm
      refine Fintype.sum_bijective (fun x : (Fin p → κ) × κ => (Fin.snoc x.1 x.2 : Fin (p + 1) → κ))
        ⟨?_, ?_⟩ _ _ fun x => rfl
      · intro x y hxy
        have h1 := congrArg Fin.init hxy
        have h2 := congrFun hxy (Fin.last p)
        simp only [Fin.init_snoc, Fin.snoc_last] at h1 h2
        exact Prod.ext h1 h2
      · intro a
        exact ⟨(Fin.init a, a (Fin.last p)), Fin.snoc_init_self a⟩
    have hmono : ∀ (a' : Fin p → κ) (b : κ), xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) =
        xnMono ι hp0 a' * X (ι b, (⟨p, hp⟩ : Fin n)) := by
      intro a' b
      unfold xnMono
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rfl
    have hstep : ∀ a' : Fin p → κ, ∑ b : κ, fockF (xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) * g)
        (initMinor ℂ (ι ∘ (Fin.snoc a' b : Fin (p + 1) → κ)) hp * f) =
        star ((Fintype.card κ : ℂ) - p + ((m p : ℕ) : ℂ)) *
          fockF (xnMono ι hp0 a' * g) (initMinor ℂ (ι ∘ a') hp0 * f) := by
      intro a'
      have hE : ∀ b : κ, xnMono ι hp (Fin.snoc a' b : Fin (p + 1) → κ) * g =
          X (ι b, (⟨p, hp⟩ : Fin n)) * (xnMono ι hp0 a' * g) := fun b => by rw [hmono]; ring
      simp only [hE, fockF_X_mul_eq_pderiv]
      rw [← fockF_sum_right', xn_key ι hι hp a' f ((m p : ℕ) : ℂ) (fun t ht => hR t ⟨p, hp⟩ ht) (hW ⟨p, hp⟩),
        fockF_C_mul_right]
    rw [hre]
    simp only [hstep, ← Finset.mul_sum]
    rw [ih]
    simp only [xnC, Finset.prod_range_succ, star_add, star_sub, star_natCast]
    push_cast
    ring

private lemma fockF_eq_sum_coeff_factorial_of_support_subset (F G : MvPolynomial (Fin r × Fin n) ℂ)
    (S : Finset ((Fin r × Fin n) →₀ ℕ)) (hS : F.support ⊆ S) :
    fockF F G = ∑ m ∈ S, F.coeff m * star (G.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  have h0 : F.coeff m = 0 := by simpa using hm
  rw [h0, zero_mul, zero_mul]

private lemma fockF_sum_left' {ι' : Type*} (s : Finset ι') (F : ι' → MvPolynomial (Fin r × Fin n) ℂ)
    (G : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (∑ i ∈ s, F i) G = ∑ i ∈ s, fockF (F i) G := by
  rw [fockF_eq_sum_coeff_factorial_of_support_subset (∑ i ∈ s, F i) G _ MvPolynomial.support_sum]
  rw [Finset.sum_congr rfl fun i hi => fockF_eq_sum_coeff_factorial_of_support_subset (F i) G (s.biUnion fun i => (F i).support)
    (Finset.subset_biUnion_of_mem (fun i => (F i).support) hi)]
  simp only [MvPolynomial.coeff_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma fockF_C_mul_left (F G : MvPolynomial (Fin r × Fin n) ℂ) (c : ℂ) :
    fockF (C c * F) G = c * fockF F G := by
  rw [fockF_eq_sum_coeff_factorial_of_support_subset (C c * F) G F.support ?_]
  · unfold fockF
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_C_mul]
    ring
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    exact MvPolynomial.mem_support_iff.2 (right_ne_zero_of_mul hm)

lemma xn_S (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) :
    ∑ a : Fin p → κ, fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f) =
      (p.factorial : ℂ) * (((xnC (Fintype.card κ) m p : ℝ) : ℂ) * fockF f f) := by
  have hT := fock_pairing_initial_minor ι hι m f hR hW p hp f
  have hterm : ∀ a : Fin p → κ, fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f) =
      ∑ π : Equiv.Perm (Fin p),
        fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) := by
    intro a
    have e := xn_minor_sum ι hp a
    calc fockF (initMinor ℂ (ι ∘ a) hp * f) (initMinor ℂ (ι ∘ a) hp * f)
        = fockF ((∑ π : Equiv.Perm (Fin p), C (xnSg π) * xnMono ι hp (a ∘ π)) * f)
            (initMinor ℂ (ι ∘ a) hp * f) := by rw [← e]
      _ = ∑ π : Equiv.Perm (Fin p),
            xnSg π * fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ a) hp * f) := by
          rw [Finset.sum_mul, fockF_sum_left']
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [mul_assoc, fockF_C_mul_left]
      _ = ∑ π : Equiv.Perm (Fin p),
            fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) := by
          refine Finset.sum_congr rfl fun π _ => ?_
          have e2 : initMinor ℂ (ι ∘ a) hp = C (xnSg π) * initMinor ℂ (ι ∘ (a ∘ π)) hp := by
            rw [xn_minor_perm ι hp a π, ← mul_assoc, ← map_mul, xnSg_mul_self, map_one, one_mul]
          rw [e2, mul_assoc, fockF_C_mul_right, xnSg_star, ← mul_assoc, xnSg_mul_self, one_mul]
  have hperm : ∀ π : Equiv.Perm (Fin p),
      ∑ a : Fin p → κ, fockF (xnMono ι hp (a ∘ π) * f) (initMinor ℂ (ι ∘ (a ∘ π)) hp * f) =
        ∑ a : Fin p → κ, fockF (xnMono ι hp a * f) (initMinor ℂ (ι ∘ a) hp * f) := by
    intro π
    exact Fintype.sum_bijective (fun a : Fin p → κ => a ∘ π)
      ⟨fun x y h => by
        funext i
        simpa using congrFun h (π.symm i),
       fun b => ⟨b ∘ π.symm, by funext i; simp⟩⟩ _ _ fun a => rfl
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_comm,
    Finset.sum_congr rfl fun π _ => hperm π, hT, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

def xnN {σ : Type*} (f : MvPolynomial σ ℂ) : ℝ := (fockF f f).re

lemma xnN_nonneg {σ : Type*} (f : MvPolynomial σ ℂ) : 0 ≤ xnN f := by
  have key : ∀ (c : ℂ) (N : ℕ), 0 ≤ (c * star c * (N : ℂ)).re := by
    intro c N
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    first
    | (simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.natCast_re, Complex.natCast_im, Complex.mul_im]
       nlinarith [sq_nonneg c.re, sq_nonneg c.im])
    | (rw [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        Complex.ofReal_re]
       exact mul_nonneg (Complex.normSq_nonneg _) hN)
  unfold xnN fockF
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun m _ => key _ _

lemma xnN_sg {σ : Type*} {p : ℕ} (π : Equiv.Perm (Fin p)) (f : MvPolynomial σ ℂ) :
    xnN (C (xnSg π) * f) = xnN f := by
  unfold xnN fockF
  have hc : xnSg π ≠ 0 := fun h0 => by simpa [h0] using xnSg_mul_self π
  rw [MvPolynomial.C_mul']
  first
  | rw [MvPolynomial.support_smul_eq hc]
  | rw [Finsupp.support_smul_eq hc]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul', xnSg_star]
  rw [show ∀ a x y N : ℂ, a * x * (a * y) * N = (a * a) * (x * y * N) from fun _ _ _ _ => by ring,
    xnSg_mul_self, one_mul]

lemma xn_SR (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) :
    ∑ a : Fin p → κ, xnN (initMinor ℂ (ι ∘ a) hp * f) =
      (p.factorial : ℝ) * (xnC (Fintype.card κ) m p * xnN f) := by
  have h := xn_S ι hι m f hR hW p hp
  unfold xnN
  rw [← Complex.re_sum, h]
  first
  | (rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul])
  | (simp [Complex.mul_re])
  | (simp [Complex.mul_re]; ring)

lemma xn_sum_perm (ι : κ → Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ) (p : ℕ) (hp : p ≤ n)
    (J : Fin p → κ) (hJ : Function.Injective J) :
    ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => J ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) = (p.factorial : ℝ) * xnN (initMinor ℂ (ι ∘ J) hp * f) := by
  rw [Finset.sum_image (by intro x _ y _ hxy; exact Equiv.ext fun i => hJ (congrFun hxy i))]
  have e : ∀ π : Equiv.Perm (Fin p), xnN (initMinor ℂ (ι ∘ (J ∘ π)) hp * f) =
      xnN (initMinor ℂ (ι ∘ J) hp * f) := by
    intro π
    rw [xn_minor_perm ι hp J π, mul_assoc, xnN_sg]
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

lemma xn_U (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) (J : Fin p → κ) (hJ : Function.Injective J) :
    xnN (initMinor ℂ (ι ∘ J) hp * f) ≤ xnC (Fintype.card κ) m p * xnN f := by
  have h1 := xn_SR ι hι m f hR hW p hp
  have h2 := xn_sum_perm ι f p hp J hJ
  have h3 : ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => J ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) ≤ ∑ a : Fin p → κ, xnN (initMinor ℂ (ι ∘ a) hp * f) :=
    Finset.sum_le_univ_sum_of_nonneg fun a => xnN_nonneg _
  rw [h1, h2] at h3
  exact le_of_mul_le_mul_left h3 (by exact_mod_cast p.factorial_pos)

lemma xn_L {p : ℕ} (ι : Fin p → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : Fin p, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : Fin p, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (hp : p ≤ n) :
    xnN (initMinor ℂ ι hp * f) = xnC p m p * xnN f := by
  have h1 := xn_SR ι hι m f hR hW p hp
  rw [Fintype.card_fin] at h1
  have h2 := xn_sum_perm ι f p hp id Function.injective_id
  have h3 : ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => id ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) = ∑ a : Fin p → Fin p, xnN (initMinor ℂ (ι ∘ a) hp * f) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
    have hna : ¬ Function.Injective (ι ∘ a) := by
      intro hinj
      apply ha
      refine Finset.mem_image.2 ⟨Equiv.ofBijective a (Finite.injective_iff_bijective.1 hinj.of_comp),
        Finset.mem_univ _, ?_⟩
      rfl
    rw [xn_minor_zero _ hp hna, zero_mul]
    simp [xnN, fockF]
  rw [← h3, h2] at h1
  have hpos : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  exact mul_left_cancel₀ hpos.ne' h1

end XiB

section XiC

variable {r n : ℕ}

lemma xn_E_X (t s : Fin n) (v : Fin r × Fin n) :
    ∑ b : Fin r, (X (b, t) : MvPolynomial (Fin r × Fin n) ℂ) * pderiv (b, s) (X v) =
      if v.2 = s then X (v.1, t) else 0 := by
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero]
  obtain ⟨v1, v2⟩ := v
  by_cases h : v2 = s
  · subst h
    simp
  · simp [h]

lemma xn_E_eq (t s : Fin n) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    ∑ b : Fin r, X (b, t) * pderiv (b, s) f = ndE ℂ r n t s f := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [MvPolynomial.derivation_C]
  next p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  next p v hp =>
    have e := xn_E_X t s v
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, ← hp]
    simp only [ndE, MvPolynomial.mkDerivation_X]
    rw [← e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring

lemma xn_Eul_eq (s : Fin n) : ndEul ℂ r n s = ndE ℂ r n s s := by
  apply MvPolynomial.derivation_ext
  intro v
  simp only [ndEul, ndE, MvPolynomial.mkDerivation_X, colW]
  obtain ⟨v1, v2⟩ := v
  by_cases h : v2 = s
  · subst h
    simp
  · simp [h, Pi.single_apply, Ne.symm h]

lemma xn_hR {μ : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n μ)
    (t s : Fin n) (hts : t < s) : ∑ b : Fin r, X (b, t) * pderiv (b, s) f = 0 := by
  have hinv := (mem_dualWeyl_iff.1 hf).2 t s hts
  set ε : MvPolynomial (Option (Fin r × Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Fin r × Fin n) ℂ :=
    aeval fun o => Option.elim o 0 X with hε
  have hεX : ∀ o, ε (X o) = Option.elim o 0 X := fun o => by rw [hε, aeval_X]
  have hεc : ∀ g, ε (colAddGen ℂ t s g) = g := by
    intro g
    have hc : ε.comp (colAddGen ℂ (r := r) t s) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [AlgHom.comp_apply, AlgHom.id_apply, colAddGen, aeval_X]
      split_ifs <;> simp [hεX]
    simpa using AlgHom.congr_fun hc g
  have hXv : ∀ v : Fin r × Fin n, ε (pderiv none (colAddGen ℂ t s (X v))) =
      if v.2 = s then X (v.1, t) else 0 := by
    intro v
    simp only [colAddGen, aeval_X]
    split_ifs
    · simp [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hεX]
    · simp [MvPolynomial.pderiv_X, Pi.single_apply]
  have hE : ∀ v : Fin r × Fin n, ndE ℂ r n t s (X v) = if v.2 = s then X (v.1, t) else 0 :=
    fun v => by simp only [ndE, MvPolynomial.mkDerivation_X]
  have key : ∀ g, ε (pderiv none (colAddGen ℂ t s g)) = ndE ℂ r n t s g := by
    intro g
    induction g using MvPolynomial.induction_on
    next a => simp [MvPolynomial.derivation_C]
    next p q hp hq => simp only [map_add, hp, hq]
    next p v hp =>
      rw [map_mul (colAddGen ℂ (r := r) t s), Derivation.leibniz (pderiv (R := ℂ) none), smul_eq_mul,
        smul_eq_mul, map_add, map_mul ε, map_mul ε, hp, hεc, hεc, hXv,
        Derivation.leibniz (ndE ℂ r n t s), smul_eq_mul, smul_eq_mul, hE]
  have hsupp : rename (some : Fin r × Fin n → Option (Fin r × Fin n)) f ∈
      MvPolynomial.supported ℂ (Set.range (some : Fin r × Fin n → Option (Fin r × Fin n))) := by
    rw [MvPolynomial.mem_supported]
    intro o ho
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ ho)
    exact ⟨v, rfl⟩
  rw [xn_E_eq, ← key, hinv, xn_pderiv_supported _ none (by simp) _ hsupp, map_zero]

lemma xn_hW {μ : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n μ)
    (s : Fin n) : ∑ b : Fin r, X (b, s) * pderiv (b, s) f = C ((μ s : ℕ) : ℂ) * f := by
  have hwh := (mem_dualWeyl_iff.1 hf).1
  rw [xn_E_eq, ← xn_Eul_eq]
  have hmono : ∀ (d : Fin r × Fin n →₀ ℕ) (c : ℂ), ndEul ℂ r n s (monomial d c) =
      C (((Finsupp.weight (colW r n) d) s : ℕ) : ℂ) * monomial d c := by
    intro d c
    induction d using Finsupp.induction
    next =>
      rw [← MvPolynomial.C_apply, MvPolynomial.derivation_C]
      simp
    next v k d hv hk ih =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [MvPolynomial.monomial_single_add, Derivation.leibniz, ih, Derivation.leibniz_pow]
      simp only [ndEul, MvPolynomial.mkDerivation_X, map_add, Pi.add_apply, Nat.add_sub_cancel]
      first
      | rw [Finsupp.weight_single_index]
      | rw [Finsupp.weight_single]
      simp only [colW, smul_eq_mul, nsmul_eq_mul, Pi.smul_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        map_add, map_mul, map_natCast, map_one]
      ring
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hmono, hwh (MvPolynomial.mem_support_iff.1 hd)]

lemma xn_sum_castLE {A : Type*} [AddCommMonoid A] {k : ℕ} (hk : k ≤ r) (g : Fin r → A)
    (hg : ∀ b : Fin r, k ≤ b.val → g b = 0) :
    ∑ b : Fin k, g (Fin.castLE hk b) = ∑ b : Fin r, g b := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hk) (f := g)
    (by intro x _ y _ hxy; exact Fin.castLE_injective hk hxy)]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro b _ hb
  apply hg
  by_contra hlt
  push_neg at hlt
  exact hb (Finset.mem_image.2 ⟨⟨b.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

lemma xn_sum_rows {k : ℕ} (hk : k ≤ r) {f : MvPolynomial (Fin r × Fin n) ℂ}
    (hs : f ∈ supported ℂ {v : Fin r × Fin n | v.1.val < k}) (t s : Fin n) :
    ∑ b : Fin k, X (Fin.castLE hk b, t) * pderiv (Fin.castLE hk b, s) f =
      ∑ b : Fin r, X (b, t) * pderiv (b, s) f := by
  refine xn_sum_castLE hk (fun b => X (b, t) * pderiv (b, s) f) ?_
  intro b hb
  show X (b, t) * pderiv (b, s) f = 0
  rw [xn_pderiv_supported _ (b, s) (by intro h; simp only [Set.mem_setOf_eq] at h; omega) f hs, mul_zero]

end XiC

section XiD

def xnT (μ : ℕ → ℕ) (i j : ℕ) : ℝ :=
  if i < j then ((μ i : ℝ) - μ j + j - i) / ((j : ℝ) - i) else 1

def xnW (N : ℕ) (μ : ℕ → ℕ) : ℝ := ∏ i ∈ Finset.range N, ∏ j ∈ Finset.range N, xnT μ i j

def xnAdd (μ : ℕ → ℕ) (p : ℕ) : ℕ → ℕ := fun j => μ j + if j < p then 1 else 0

lemma xn_R (μ : ℕ → ℕ) (p i : ℕ) (hi : i < p) (h0 : ∀ j, p ≤ j → μ j = 0) (m : ℕ) (hm : p ≤ m) :
    (∏ j ∈ Finset.range m, xnT (xnAdd μ p) i j) * ((p : ℝ) - i + μ i) =
      (∏ j ∈ Finset.range m, xnT μ i j) * ((m : ℝ) - i + μ i) := by
  have hlt : ∀ j, j < p → xnT (xnAdd μ p) i j = xnT μ i j := by
    intro j hj
    simp only [xnT, xnAdd, if_pos hi, if_pos hj]
    split_ifs <;> push_cast <;> ring
  obtain ⟨d, rfl⟩ : ∃ d, m = p + d := ⟨m - p, by omega⟩
  clear hm
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    rw [Finset.prod_congr rfl fun j hj => hlt j (Finset.mem_range.1 hj)]
  | succ d ih =>
    have hμ : μ (p + d) = 0 := h0 _ (by omega)
    have h1 : i < p + d := by omega
    have h2 : ¬ (p + d < p) := by omega
    have e1 : xnT (xnAdd μ p) i (p + d) =
        ((μ i : ℝ) + 1 + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i) := by
      simp only [xnT, xnAdd, if_pos h1, if_pos hi, if_neg h2, hμ]
      push_cast
      ring
    have e2 : xnT μ i (p + d) = ((μ i : ℝ) + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i) := by
      simp only [xnT, if_pos h1, hμ]
      push_cast
      ring
    rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_range_succ, e1, e2]
    push_cast at ih ⊢
    linear_combination (((μ i : ℝ) + 1 + ((p : ℝ) + d) - i) / (((p : ℝ) + d) - i)) * ih

lemma xn_R' (μ : ℕ → ℕ) (p i : ℕ) (hi : p ≤ i) (m : ℕ) :
    (∏ j ∈ Finset.range m, xnT (xnAdd μ p) i j) = ∏ j ∈ Finset.range m, xnT μ i j := by
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : ¬ i < p := by omega
  by_cases hij : i < j
  · have h2 : ¬ j < p := by omega
    simp only [xnT, xnAdd, if_pos hij, if_neg h1, if_neg h2, Nat.add_zero]
  · simp only [xnT, if_neg hij]

lemma xnC_ite (M : ℕ) (m : ℕ → ℕ) (p N : ℕ) (hp : p ≤ N) :
    xnC M m p = ∏ i ∈ Finset.range N, if i < p then ((M : ℝ) - i + m i) else 1 := by
  unfold xnC
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

lemma xn_W_ratio (N : ℕ) (μ : ℕ → ℕ) (p : ℕ) (hp : p ≤ N) (h0 : ∀ j, p ≤ j → μ j = 0) :
    xnW N (xnAdd μ p) * xnC p μ p = xnW N μ * xnC N μ p := by
  rw [xnC_ite p μ p N hp, xnC_ite N μ p N hp]
  unfold xnW
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i < p
  · simp only [if_pos hi]
    exact xn_R μ p i hi h0 N hp
  · simp only [if_neg hi, mul_one]
    exact xn_R' μ p i (by omega) N

lemma xnW_zero (N : ℕ) : xnW N (fun _ => 0) = 1 := by
  unfold xnW xnT
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs with h
  · have hij : (i : ℝ) < j := by exact_mod_cast h
    rw [div_eq_one_iff_eq (by linarith)]
    simp
  · rfl

lemma xnW_weylProd (n : ℕ) (μ : ℕ → ℕ) :
    weylProd (fun a : Fin (n + 1) => ((μ a.val : ℕ) : ℤ)) = xnW (n + 1) μ := by
  unfold weylProd xnW
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [Finset.prod_range]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  simp only [xnT, Fin.lt_iff_val_lt_val]
  split_ifs <;> push_cast <;> ring

lemma xnC_nonneg (M : ℕ) (m : ℕ → ℕ) (p : ℕ) (hp : p ≤ M) : 0 ≤ xnC M m p := by
  unfold xnC
  refine Finset.prod_nonneg fun q hq => ?_
  have hq' : q < p := Finset.mem_range.1 hq
  have h1 : (q : ℝ) ≤ M := by exact_mod_cast (by omega : q ≤ M)
  have h2 : (0 : ℝ) ≤ m q := Nat.cast_nonneg _
  linarith

end XiD

section XiE

variable {r n : ℕ}

structure xnInv (k : ℕ) (μ : ℕ → ℕ) (x h : MvPolynomial (Fin r × Fin n) ℂ) : Prop where
  supp : ∀ q, k ≤ q → μ q = 0
  xm : x ∈ dualWeyl ℂ r n (fun q => μ q.val)
  hm : h ∈ dualWeyl ℂ r n (fun q => μ q.val)
  hs : h ∈ supported ℂ {v : Fin r × Fin n | v.1.val < k}
  le : xnN x ≤ xnW r μ * xnN h

lemma xnInv_congr {k : ℕ} {μ μ' : ℕ → ℕ} {x x' h h' : MvPolynomial (Fin r × Fin n) ℂ}
    (H : xnInv k μ x h) (e1 : μ = μ') (e2 : x = x') (e3 : h = h') : xnInv k μ' x' h' := by
  subst e1
  subst e2
  subst e3
  exact H

lemma xnInv_zero : xnInv 0 (fun _ => 0) (1 : MvPolynomial (Fin r × Fin n) ℂ) 1 := by
  have h1 : (1 : MvPolynomial (Fin r × Fin n) ℂ) ∈ dualWeyl ℂ r n (fun q => (fun _ => 0) q.val) :=
    one_mem_dualWeyl
  exact ⟨fun q _ => rfl, h1, h1, one_mem _, le_of_eq (by rw [xnW_zero, one_mul])⟩

lemma xnInv_mono {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h) :
    xnInv (k + 1) μ x h := by
  exact { supp := fun q hq => H.supp q (by omega), xm := H.xm, hm := H.hm,
          hs := MvPolynomial.supported_mono
            (fun v hv => by simp only [Set.mem_setOf_eq] at hv ⊢; omega) H.hs,
          le := H.le }

lemma xnInv_step {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h)
    (hk : k ≤ n) (hkr : k ≤ r) (J : Fin k → Fin r) (hJ : Function.Injective J) :
    xnInv k (xnAdd μ k) (initMinor ℂ J hk * x) (lpMinor ℂ k hkr hk * h) := by
  have hw : initW n k + (fun q : Fin n => μ q.val) = fun q : Fin n => xnAdd μ k q.val := by
    funext q
    simp only [initW, xnAdd, Pi.add_apply]
    split_ifs <;> omega
  have hL0 : lpMinor ℂ k hkr hk = initMinor ℂ (Fin.castLE hkr) hk := rfl
  have hLm : lpMinor ℂ k hkr hk ∈ dualWeyl ℂ r n (initW n k) := by
    rw [hL0]
    exact initMinor_mem _ _
  have hRx : ∀ t s : Fin n, t < s →
      ∑ b : Fin r, X ((id : Fin r → Fin r) b, t) * pderiv ((id : Fin r → Fin r) b, s) x = 0 :=
    fun t s hts => xn_hR H.xm t s hts
  have hWx : ∀ s : Fin n, ∑ b : Fin r, X ((id : Fin r → Fin r) b, s) *
      pderiv ((id : Fin r → Fin r) b, s) x = C ((μ s.val : ℕ) : ℂ) * x :=
    fun s => xn_hW H.xm s
  have hRh : ∀ t s : Fin n, t < s →
      ∑ b : Fin k, X (Fin.castLE hkr b, t) * pderiv (Fin.castLE hkr b, s) h = 0 :=
    fun t s hts => by
      rw [xn_sum_rows hkr H.hs]
      exact xn_hR H.hm t s hts
  have hWh : ∀ s : Fin n, ∑ b : Fin k, X (Fin.castLE hkr b, s) * pderiv (Fin.castLE hkr b, s) h =
      C ((μ s.val : ℕ) : ℂ) * h :=
    fun s => by
      rw [xn_sum_rows hkr H.hs]
      exact xn_hW H.hm s
  have hU := xn_U (id : Fin r → Fin r) Function.injective_id μ x hRx hWx k hk J hJ
  rw [Fintype.card_fin] at hU
  have hLeq := xn_L (Fin.castLE hkr) (Fin.castLE_injective hkr) μ h hRh hWh hk
  rw [← hL0] at hLeq
  have hR := xn_W_ratio r μ k hkr H.supp
  have hC := xnC_nonneg r μ k hkr
  refine ⟨fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xnAdd, if_neg (show ¬ q < k by omega), Nat.add_zero]
    exact H.supp q hq
  · rw [← hw]
    exact dualWeyl_mul (initMinor_mem J hk) H.xm
  · rw [← hw]
    exact dualWeyl_mul hLm H.hm
  · refine mul_mem ?_ H.hs
    rw [hL0]
    unfold initMinor
    refine xn_det_supported _ _ fun i j => ?_
    rw [Matrix.of_apply]
    first
    | exact (MvPolynomial.X_mem_supported (R := ℂ)).2 (show (Fin.castLE hkr i).val < k from i.isLt)
    | exact MvPolynomial.X_mem_supported.mpr (show (Fin.castLE hkr i).val < k from i.isLt)
  · rw [hLeq]
    calc xnN (initMinor ℂ J hk * x) ≤ xnC r μ k * xnN x := hU
      _ ≤ xnC r μ k * (xnW r μ * xnN h) := mul_le_mul_of_nonneg_left H.le hC
      _ = (xnW r μ * xnC r μ k) * xnN h := by ring
      _ = (xnW r (xnAdd μ k) * xnC k μ k) * xnN h := by rw [hR]
      _ = xnW r (xnAdd μ k) * (xnC k μ k * xnN h) := by ring

lemma xnInv_pow {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h)
    (hk : k ≤ n) (hkr : k ≤ r) (J : Fin k → Fin r) (hJ : Function.Injective J) (e : ℕ) :
    xnInv k (fun q => μ q + if q < k then e else 0) (initMinor ℂ J hk ^ e * x)
      (lpMinor ℂ k hkr hk ^ e * h) := by
  induction e with
  | zero =>
    refine xnInv_congr H ?_ ?_ ?_
    · funext q
      split_ifs <;> simp
    · simp
    · simp
  | succ e ih =>
    have H2 := xnInv_step ih hk hkr J hJ
    refine xnInv_congr H2 ?_ ?_ ?_
    · funext q
      simp only [xnAdd]
      split_ifs <;> omega
    · ring
    · ring

end XiE

section XiF

def xnLam {n : ℕ} (lam : Fin n → ℕ) (q : ℕ) : ℕ := if h : q < n then lam ⟨q, h⟩ else 0

lemma xn_rowsA_inj {n : ℕ} (i : Fin n) : Function.Injective (rowsA i) := by
  intro x y h
  simp only [rowsA, Fin.mk.injEq] at h
  exact Fin.ext h

lemma xn_rowsB_inj {n : ℕ} (i : Fin n) : Function.Injective (rowsB i) := by
  intro x y h
  have hx := x.isLt
  have hy := y.isLt
  have hi := i.isLt
  simp only [rowsB] at h
  apply Fin.ext
  split_ifs at h
  all_goals first
    | (simpa using h)
    | (have h' := congrArg Fin.val h
       simp only [Fin.val_last, Fin.val_mk] at h'
       omega)
    | omega

lemma xn_interlace {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (i : Fin n) : nuNext lam i ≤ sg i ∧ sg i ≤ lam i := by
  obtain ⟨h1, h2⟩ := hI i
  have hi := i.isLt
  simp only [lamZ, Fin.coe_castSucc, Fin.val_succ] at h1 h2
  rw [dif_pos hi] at h1
  unfold nuNext
  constructor
  · split_ifs with hh
    · rw [dif_pos hh] at h2
      exact_mod_cast h2
    · exact Nat.zero_le _
  · exact_mod_cast h1

lemma xnLam_anti {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    Antitone (xnLam lam) := by
  refine antitone_nat_of_succ_le fun q => ?_
  unfold xnLam
  by_cases h1 : q + 1 < n
  · have h0 : q < n := by omega
    rw [dif_pos h1, dif_pos h0]
    obtain ⟨ha, hb⟩ := xn_interlace lam sg hI ⟨q, h0⟩
    unfold nuNext at ha
    rw [dif_pos h1] at ha
    exact le_trans ha hb
  · rw [dif_neg h1]
    exact Nat.zero_le _

lemma xn_stage (n : ℕ) (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (k : ℕ) (hk : k ≤ n) :
    xnInv (r := n + 1) (n := n) k (fun q => xnLam lam q - xnLam lam k)
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
        (initMinor ℂ (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
          initMinor ℂ (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i)))
      (∏ s ∈ Finset.univ.filter (fun s : Fin n => s.val < k),
        (lpMinor ℂ (s.val + 1) (by omega) (by omega)) ^ (lam s - nuNext lam s)) := by
  induction k with
  | zero =>
    refine xnInv_congr (xnInv_zero (r := n + 1) (n := n)) ?_ ?_ ?_
    · funext q
      have := xnLam_anti lam sg hI (Nat.zero_le q)
      show 0 = xnLam lam q - xnLam lam 0
      omega
    · simp
    · simp
  | succ k ih =>
    have hkn : k < n := by omega
    have H0 := xnInv_mono (ih (by omega))
    have H1 := xnInv_pow H0 hk (by omega) (rowsA ⟨k, hkn⟩) (xn_rowsA_inj _)
      (sg ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩)
    have H2 := xnInv_pow H1 hk (by omega) (rowsB ⟨k, hkn⟩) (xn_rowsB_inj _)
      (lam ⟨k, hkn⟩ - sg ⟨k, hkn⟩)
    obtain ⟨i1, i2⟩ := xn_interlace lam sg hI ⟨k, hkn⟩
    have hf : (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
        insert ⟨k, hkn⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff,
        Fin.val_mk]
      constructor <;> intro h <;> omega
    have hnot : (⟨k, hkn⟩ : Fin n) ∉ (Finset.univ.filter fun i : Fin n => i.val < k) := by simp
    refine xnInv_congr H2 ?_ ?_ ?_
    · funext q
      have e1 : xnLam lam k = lam ⟨k, hkn⟩ := by simp [xnLam, hkn]
      have e2 : xnLam lam (k + 1) = nuNext lam ⟨k, hkn⟩ := by
        simp only [xnLam, nuNext, Fin.val_mk]
      have a1 := xnLam_anti lam sg hI (Nat.le_succ k)
      by_cases hq : q < k + 1
      · have a2 := xnLam_anti lam sg hI (show q ≤ k by omega)
        simp only [if_pos hq]
        omega
      · have a2 := xnLam_anti lam sg hI (show k + 1 ≤ q by omega)
        simp only [if_neg hq]
        omega
    · rw [hf, Finset.prod_insert hnot]
      ring
    · have hexp : (lam ⟨k, hkn⟩ - sg ⟨k, hkn⟩) + (sg ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩) =
          lam ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩ := by omega
      rw [hf, Finset.prod_insert hnot, ← mul_assoc, ← pow_add, hexp]

end XiF

theorem xi_norm_bound : XiNorm := by
  unfold XiNorm
  intro n lam sg hI
  have H := xn_stage n lam sg hI n le_rfl
  have hμ : (fun q => xnLam lam q - xnLam lam n) = xnLam lam := by
    funext q
    have h0 : xnLam lam n = 0 := by simp [xnLam]
    rw [h0, Nat.sub_zero]
  have hx : (∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < n),
      (initMinor ℂ (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
        initMinor ℂ (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i))) = xiB ℂ lam sg := by
    unfold xiB
    rw [Finset.filter_true_of_mem fun i _ => i.isLt]
  have hh : (∏ s ∈ Finset.univ.filter (fun s : Fin n => s.val < n),
      (lpMinor ℂ (r := n + 1) (n := n) (s.val + 1) (by omega) (by omega)) ^ (lam s - nuNext lam s)) =
      hw ℂ (Nat.le_succ n) lam := by
    unfold hw
    rw [Finset.filter_true_of_mem fun i _ => i.isLt]
  have hW : weylProd (lamZ lam) = xnW (n + 1) (xnLam lam) := by
    rw [← xnW_weylProd]
    congr 1
    funext a
    simp only [lamZ, xnLam]
    split_ifs <;> simp
  have H2 := H.le
  rw [hμ, hx, hh] at H2
  unfold xnN at H2
  rw [hW]
  exact H2

end Formalism.BranchingDeterminantCap

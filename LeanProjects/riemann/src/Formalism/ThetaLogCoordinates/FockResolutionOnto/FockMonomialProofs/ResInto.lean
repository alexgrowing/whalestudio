import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementC
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.FirstWeightLeOfSupport

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Res
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem resL_keep_supp (v : σ) (e : ℕ) (Q : Set (σ →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, resL p v e x ∈ restrictSupport ℚ_[p] Q := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  intro m hm
  apply hx
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff] at hm ⊢
  change (initPart v e x).coeff m ≠ 0 at hm
  rw [coeff_initPart] at hm
  split_ifs at hm with h
  · exact hm
  · exact absurd rfl hm

theorem resL_free (v : σ) (x : MvPolynomial σ ℚ_[p]) : resL p v 0 x ∈ FreeOf p v := by
  rw [FreeOf, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff] at hm
  change (initPart v 0 x).coeff m ≠ 0 at hm
  rw [coeff_initPart] at hm
  split_ifs at hm with h
  · exact h
  · exact absurd rfl hm

theorem resL_X_mul (v u : σ) (huv : u ≠ v) (e : ℕ) (g : MvPolynomial σ ℚ_[p]) :
    resL p v e (X u * g) = X u * resL p v e g := by
  classical
  ext m
  change (initPart v e (X u * g)).coeff m = (X u * initPart v e g).coeff m
  rw [coeff_initPart, MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_mul']
  by_cases hu : u ∈ m.support
  · have hmv : (m - Finsupp.single u 1 : σ →₀ ℕ) v = m v := by
      simp [Finsupp.single_apply, huv]
    simp only [hu, if_true, coeff_initPart, hmv]
  · simp only [hu, if_false]
    split_ifs <;> rfl

theorem resL_pderiv (v u : σ) (huv : u ≠ v) (e : ℕ) (g : MvPolynomial σ ℚ_[p]) :
    resL p v e (pderiv u g) = pderiv u (resL p v e g) := by
  classical
  have hr : ∀ y, resL p v e y = initPart v e y := fun _ => rfl
  have hi : ∀ (m : σ →₀ ℕ) (a : ℚ_[p]),
      initPart v e (monomial m a) = if m v = e then monomial m a else 0 := by
    intro m a
    by_cases ha : a = 0
    · subst ha
      simp [initPart]
    · rw [initPart, MvPolynomial.support_monomial, if_neg ha, Finset.sum_singleton,
        MvPolynomial.coeff_monomial, if_pos rfl]
  induction g using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [hr, hr, MvPolynomial.pderiv_monomial, hi, hi]
    have hmv : (m - Finsupp.single u 1 : σ →₀ ℕ) v = m v := by
      simp [Finsupp.single_apply, huv]
    rw [hmv]
    split_ifs <;> simp [MvPolynomial.pderiv_monomial]
  | add f g hf hg =>
    simp only [map_add, hf, hg]

theorem resL_glAct {N r : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r) (v : Fin N × Fin r) (e : ℕ)
    (h : ∀ i : Fin N, (i : ℕ) < j → (i, c) ≠ v ∧ (i, d) ≠ v) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p v e (glAct p LL j c d x) = glAct p LL j c d (resL p v e x) := by
  classical
  rw [glAct, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : (i : ℕ) < j
  · obtain ⟨hc, hd⟩ := h i hij
    by_cases hv : LL.vec i
    · simp only [hij, hv, if_true, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [resL_X_mul v (i, c) hc]
      exact congrArg (X (i, c) * ·) (resL_pderiv v (i, d) hd e x)
    · simp only [hij, hv, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, map_neg]
      rw [resL_X_mul v (i, d) hd]
      exact congrArg (fun y => -(X (i, d) * y)) (resL_pderiv v (i, c) hc e x)
  · simp [hij]

end Res

section Last
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem wt_congr {N : ℕ} (LL : Letters N) (j : ℕ) (c : Fin r) (m m' : Fin N × Fin r →₀ ℕ)
    (h : ∀ i : Fin N, (i : ℕ) < j → m (i, c) = m' (i, c)) : wt LL j c m = wt LL j c m' := by
  simp only [wt]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < j
  · simp [h1, h i h1]
  · simp [h1]

theorem glAct_succ (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c d : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL (K + 1) c d x = glAct p LL K c d x + X (Fin.last K, c) * pderiv (Fin.last K, d) x := by
  have h1 : ∀ i : Fin K, ((Fin.castSucc i : Fin (K + 1)) : ℕ) < K + 1 := fun i => by
    simp only [Fin.coe_castSucc]
    omega
  have h2 : ∀ i : Fin K, ((Fin.castSucc i : Fin (K + 1)) : ℕ) < K := fun i => by
    simp only [Fin.coe_castSucc]
    exact i.is_lt
  rw [glAct, glAct, LinearMap.sum_apply, LinearMap.sum_apply, Fin.sum_univ_castSucc,
    Fin.sum_univ_castSucc]
  simp only [h1, h2, if_true, Fin.val_last, lt_self_iff_false, if_false, Nat.lt_succ_self, hv,
    LinearMap.zero_apply, add_zero, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rfl

theorem wt_succ (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : Fin r)
    (m : Fin (K + 1) × Fin r →₀ ℕ) : wt LL (K + 1) c m = wt LL K c m + (m (Fin.last K, c) : ℤ) := by
  have h1 : ∀ i : Fin K, ((Fin.castSucc i : Fin (K + 1)) : ℕ) < K + 1 := fun i => by
    simp only [Fin.coe_castSucc]
    omega
  have h2 : ∀ i : Fin K, ((Fin.castSucc i : Fin (K + 1)) : ℕ) < K := fun i => by
    simp only [Fin.coe_castSucc]
    exact i.is_lt
  simp only [wt, Fin.sum_univ_castSucc, h1, h2, if_true, Fin.val_last, lt_self_iff_false, if_false,
    Nat.lt_succ_self, hv, add_zero]

theorem last_ne_of_lt (i : Fin (K + 1)) (hi : (i : ℕ) < K) : Fin.last K ≠ i := by
  intro h
  rw [← h, Fin.val_last] at hi
  exact lt_irrefl _ hi

theorem disj_last : Disjoint {v : Fin (K + 1) × Fin r | K ≤ (v.1 : ℕ)} {v : Fin (K + 1) × Fin r | (v.1 : ℕ) < K} := by
  rw [Set.disjoint_left]
  intro v h1 h2
  simp only [Set.mem_setOf_eq] at h1 h2
  omega

theorem last_mem (c : Fin r) : ((Fin.last K, c) : Fin (K + 1) × Fin r) ∈ {v : Fin (K + 1) × Fin r | K ≤ (v.1 : ℕ)} := by
  simp

theorem pderiv_keep_wt [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : Fin r)
    (Mt : WithTop ℤ) :
    ∀ x ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      pderiv (Fin.last K, c) x ∈
        restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.mem_restrictSupport_iff]
  refine (Finset.coe_subset.2 MvPolynomial.support_monomial_subset).trans ?_
  rw [Finset.coe_singleton, Set.singleton_subset_iff]
  have hmx := hx hm
  simp only [Set.mem_setOf_eq] at hmx ⊢
  refine le_trans ?_ hmx
  have hle : wt LL (K + 1) 0 (m - Finsupp.single (Fin.last K, c) 1) ≤ wt LL (K + 1) 0 m := by
    rw [wt_succ LL hv, wt_succ LL hv,
      wt_congr LL K 0 (m - Finsupp.single (Fin.last K, c) 1) m ?_]
    · have h3 : (m - Finsupp.single (Fin.last K, c) 1 : Fin (K + 1) × Fin r →₀ ℕ) (Fin.last K, 0) ≤
          m (Fin.last K, 0) := by
        rw [Finsupp.tsub_apply]
        exact Nat.sub_le _ _
      omega
    · intro i hi
      have hne : ((Fin.last K, c) : Fin (K + 1) × Fin r) ≠ (i, 0) :=
        fun h => last_ne_of_lt i hi (congrArg Prod.fst h)
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
  exact_mod_cast hle

private theorem pderiv_last_glAct_comm (LL : Letters (K + 1)) (a b c : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, c) (glAct p LL K a b x) = glAct p LL K a b (pderiv (Fin.last K, c) x) := by
  classical
  rw [glAct, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : (i : ℕ) < K
  · have hne : ∀ d : Fin r, ((i, d) : Fin (K + 1) × Fin r) ≠ (Fin.last K, c) :=
      fun d h => last_ne_of_lt i hij (congrArg Prod.fst h).symm
    by_cases hv : LL.vec i
    · simp only [hij, hv, if_true, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (hne a), smul_zero, add_zero, smul_eq_mul]
      exact congrArg (X (i, a) * ·) (Formalism.GM.ProjS.pderiv_comm (Fin.last K, c) (i, b) x)
    · simp only [hij, hv, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, map_neg]
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (hne b), smul_zero, add_zero, smul_eq_mul]
      exact congrArg (fun y => -(X (i, b) * y)) (Formalism.GM.ProjS.pderiv_comm (Fin.last K, c) (i, a) x)
  · simp [hij]

theorem pderiv_glAct (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (a b c : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, c) (glAct p LL (K + 1) a b x) =
      glAct p LL (K + 1) a b (pderiv (Fin.last K, c) x) + (if a = c then pderiv (Fin.last K, b) x else 0) := by
  classical
  rw [glAct_succ LL hv, glAct_succ LL hv, map_add, pderiv_last_glAct_comm, Derivation.leibniz,
    MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul,
    Formalism.GM.ProjS.pderiv_comm (Fin.last K, c) (Fin.last K, b) x]
  by_cases hac : a = c
  · subst hac
    simp only [Pi.single_eq_same, mul_one, if_true]
    ring
  · simp [Pi.single_apply, hac, add_assoc]

private theorem yCond_le_restrictSupport_wt_le {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p LL j Mt ≤
      restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1

private theorem glAct_mem_yCond_of_neZero {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (a b : Fin r) : ∀ y ∈ YCond p LL j Mt, glAct p LL j a b y ∈ YCond p LL j Mt := by
  have h : YCond p LL j Mt ≤ (YCond p LL j Mt).comap (glAct p LL j a b) :=
    sSup_le fun _ hS y hy => le_sSup hS (hS.2 a b y hy)
  exact fun y hy => h hy

theorem ycond_pderiv [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ)
    (c : Fin r) : ∀ x ∈ YCond p LL (K + 1) Mt, pderiv (Fin.last K, c) x ∈ YCond p LL (K + 1) Mt := by
  intro x hx
  let G : Set (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    {y | ∃ c' : Fin r, ∃ z ∈ YCond p LL (K + 1) Mt, y = pderiv (Fin.last K, c') z}
  have hSle : Submodule.span ℚ_[p] G ≤ restrictSupport ℚ_[p]
      {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [Submodule.span_le]
    rintro y ⟨c', z, hz, rfl⟩
    exact pderiv_keep_wt LL hv c' Mt z (yCond_le_restrictSupport_wt_le LL (K + 1) Mt hz)
  have hSst : GlStable p LL (K + 1) (Submodule.span ℚ_[p] G) := by
    intro a b y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c', z, hz, rfl⟩ := hy
      have e := pderiv_glAct LL hv a b c' z
      rw [eq_sub_of_add_eq e.symm]
      refine Submodule.sub_mem _
        (Submodule.subset_span ⟨c', _, glAct_mem_yCond_of_neZero LL (K + 1) Mt a b z hz, rfl⟩) ?_
      split_ifs
      · exact Submodule.subset_span ⟨b, z, hz, rfl⟩
      · exact Submodule.zero_mem _
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add y1 y2 _ _ h1 h2 =>
      rw [map_add]
      exact Submodule.add_mem _ h1 h2
    | smul t y _ h =>
      rw [map_smul]
      exact Submodule.smul_mem _ t h
  exact le_ycond LL (K + 1) Mt _ hSle hSst (Submodule.subset_span ⟨c, x, hx, rfl⟩)

noncomputable def FreeLast (p : ℕ) [Fact p.Prime] (K r : ℕ) :
    Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  restrictSupport ℚ_[p] {m | ∀ c, m (Fin.last K, c) = 0}

theorem pderiv_freeLast (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ FreeLast p K r) (d : Fin r) :
    pderiv (Fin.last K, d) x = 0 := by
  rw [FreeLast, MvPolynomial.mem_restrictSupport_iff] at hx
  rw [x.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  have h0 : m (Fin.last K, d) = 0 := hx hm d
  rw [MvPolynomial.pderiv_monomial, h0]
  simp

private theorem pderiv_mem_freeLast (v : Fin (K + 1) × Fin r) :
    ∀ y ∈ FreeLast p K r, pderiv v y ∈ FreeLast p K r := by
  intro y hy
  rw [FreeLast, MvPolynomial.mem_restrictSupport_iff] at hy
  rw [y.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.pderiv_monomial, FreeLast, MvPolynomial.mem_restrictSupport_iff]
  refine (Finset.coe_subset.2 MvPolynomial.support_monomial_subset).trans ?_
  rw [Finset.coe_singleton, Set.singleton_subset_iff]
  intro c
  rw [Finsupp.tsub_apply, hy hm c, Nat.zero_sub]

private theorem X_mul_mem_freeLast_of_ne_last (v : Fin (K + 1) × Fin r) (hv : v.1 ≠ Fin.last K) :
    ∀ y ∈ FreeLast p K r, X v * y ∈ FreeLast p K r := by
  classical
  intro y hy
  rw [FreeLast, MvPolynomial.mem_restrictSupport_iff] at hy ⊢
  intro m hm c
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul'] at hm
  split_ifs at hm with hmem
  · have h1 := hy (MvPolynomial.mem_support_iff.2 hm) c
    have hne : v ≠ (Fin.last K, c) := fun h => hv (congrArg Prod.fst h)
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero] at h1
    exact h1
  · exact absurd rfl hm

private theorem glAct_mem_freeLast (LL : Letters (K + 1)) (a b : Fin r) :
    ∀ y ∈ FreeLast p K r, glAct p LL K a b y ∈ FreeLast p K r := by
  intro y hy
  rw [glAct, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hij : (i : ℕ) < K
  · have hi : i ≠ Fin.last K := fun h => last_ne_of_lt i hij h.symm
    by_cases hvi : LL.vec i
    · simp only [hij, hvi, if_true, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact X_mul_mem_freeLast_of_ne_last (i, a) hi _ (pderiv_mem_freeLast (i, b) y hy)
    · simp only [hij, hvi, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact Submodule.neg_mem _ (X_mul_mem_freeLast_of_ne_last (i, b) hi _ (pderiv_mem_freeLast (i, a) y hy))
  · simp only [hij, if_false, LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem free_le_ycond [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ) :
    YCond p LL (K + 1) Mt ⊓ FreeLast p K r ≤ YCond p LL K Mt := by
  rintro y ⟨hY, hF⟩
  refine le_ycond LL K Mt (YCond p LL (K + 1) Mt ⊓ FreeLast p K r) ?_ ?_ ⟨hY, hF⟩
  · rintro z ⟨hzY, hzF⟩
    have h1 := yCond_le_restrictSupport_wt_le LL (K + 1) Mt hzY
    rw [MvPolynomial.mem_restrictSupport_iff] at h1 ⊢
    rw [FreeLast, SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff] at hzF
    intro m hm
    have hw := h1 hm
    have h0 : m (Fin.last K, 0) = 0 := hzF hm 0
    simp only [Set.mem_setOf_eq] at hw ⊢
    rw [wt_succ LL hv, h0, Nat.cast_zero, add_zero] at hw
    exact hw
  · rintro a b z ⟨hzY, hzF⟩
    have e := glAct_succ LL hv a b z
    rw [pderiv_freeLast z hzF b, mul_zero, add_zero] at e
    refine ⟨?_, glAct_mem_freeLast LL a b z hzF⟩
    rw [← e]
    exact glAct_mem_yCond_of_neZero LL (K + 1) Mt a b z hzY

private theorem glAct_X_last_mul_eq (LL : Letters (K + 1)) (a b c : Fin r)
    (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL K a b (X (Fin.last K, c) * y) = X (Fin.last K, c) * glAct p LL K a b y := by
  classical
  rw [glAct, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : (i : ℕ) < K
  · have hne : ∀ d : Fin r, ((Fin.last K, c) : Fin (K + 1) × Fin r) ≠ (i, d) :=
      fun d h => last_ne_of_lt i hij (congrArg Prod.fst h)
    by_cases hvi : LL.vec i
    · simp only [hij, hvi, if_true, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        Derivation.coeFn_coe]
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (hne b), smul_zero, add_zero, smul_eq_mul]
      ring
    · simp only [hij, hvi, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (hne a), smul_zero, add_zero, smul_eq_mul]
      ring
  · simp [hij]

private theorem X_last_mul_mem_restrictSupport_wt_le [NeZero r] (LL : Letters (K + 1)) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ y ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL K 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      X (Fin.last K, c) * y ∈
        restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL K 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
  classical
  intro y hy
  rw [MvPolynomial.mem_restrictSupport_iff] at hy ⊢
  intro m hm
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul'] at hm
  split_ifs at hm with hmem
  · have h1 := hy (MvPolynomial.mem_support_iff.2 hm)
    simp only [Set.mem_setOf_eq] at h1 ⊢
    rwa [wt_congr LL K 0 m (m - Finsupp.single (Fin.last K, c) 1)]
    intro i hi
    have hne : ((Fin.last K, c) : Fin (K + 1) × Fin r) ≠ (i, 0) :=
      fun h => last_ne_of_lt i hi (congrArg Prod.fst h)
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
  · exact absurd rfl hm

theorem mulX_ycond [NeZero r] (LL : Letters (K + 1)) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL K Mt, X (Fin.last K, c) * x ∈ YCond p LL K Mt := by
  intro x hx
  refine le_ycond LL K Mt ((YCond p LL K Mt).map (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, c))))
    ?_ ?_ ⟨x, hx, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact X_last_mul_mem_restrictSupport_wt_le LL Mt c y (yCond_le_restrictSupport_wt_le LL K Mt hy)
  · rintro a b _ ⟨y, hy, rfl⟩
    refine ⟨glAct p LL K a b y, glAct_mem_yCond_of_neZero LL K Mt a b y hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    exact (glAct_X_last_mul_eq LL a b c y).symm

private theorem pderiv_last_eulL_eq (c : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, c) (Formalism.GM.ProjS.eulL (fun d : Fin r => (Fin.last K, d)) g) =
      pderiv (Fin.last K, c) g +
        Formalism.GM.ProjS.eulL (fun d : Fin r => (Fin.last K, d)) (pderiv (Fin.last K, c) g) := by
  classical
  rw [Formalism.GM.ProjS.eulL_apply, Formalism.GM.ProjS.eulL_apply, map_sum]
  simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, Finset.sum_add_distrib]
  refine (add_comm _ _).trans ?_
  congr 1
  · rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      have hne : ((Fin.last K, d) : Fin (K + 1) × Fin r) ≠ (Fin.last K, c) := by simp [hd]
      simp [Pi.single_apply, hne]
    · intro h
      exact absurd (Finset.mem_univ c) h
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Formalism.GM.ProjS.pderiv_comm]

theorem mem_cond_of_euler_eigen [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ) :
    ∀ (o : ℕ) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), F ∈ YCond p LL (K + 1) Mt →
      ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F = ((o : ℕ) : ℚ_[p]) • F → F ∈ YCond p LL K Mt := by
  intro o
  induction o with
  | zero =>
    intro F hF he
    apply free_le_ycond LL hv Mt
    refine ⟨hF, ?_⟩
    rw [FreeLast, SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
    intro m hm c
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff] at hm
    have hc := congrArg (MvPolynomial.coeff m) he
    rw [Formalism.GM.ProjS.coeff_eulL, Nat.cast_zero, zero_smul, MvPolynomial.coeff_zero] at hc
    have hs : (∑ d : Fin r, (m (Fin.last K, d) : ℚ_[p])) = 0 := (mul_eq_zero.1 hc).resolve_left hm
    have hs' : ∑ d : Fin r, m (Fin.last K, d) = 0 := by exact_mod_cast hs
    exact (Finset.sum_eq_zero_iff.1 hs') c (Finset.mem_univ c)
  | succ o ih =>
    intro F hF he
    have hne : ((o + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero o
    have hF' : F = ((o + 1 : ℕ) : ℚ_[p])⁻¹ • Formalism.GM.ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F := by
      rw [he, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hF', Formalism.GM.ProjS.eulL_apply]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c _ => mulX_ycond LL Mt c _ (ih _
      (ycond_pderiv LL hv Mt c F hF) ?_))
    have hcomm := pderiv_last_eulL_eq c F
    rw [he, Derivation.map_smul] at hcomm
    rw [eq_sub_of_add_eq' hcomm.symm]
    push_cast
    rw [add_smul, one_smul, add_sub_cancel_right]

end Last

theorem condition_drop_holds : YCondDrop := by
  intro p _ K r _ LL M hv F hF hY
  exact mem_cond_of_euler_eigen LL hv M (LL.deg (Fin.last K)) F hY ((pol_iff_eul LL F).1 hF (Fin.last K))

theorem restriction_into_holds : ResInto := by
  intro p _ K r _ LL q J M ρ e1 hr hρ hv hHP h hh
  obtain ⟨hhP, hhY⟩ := Submodule.mem_inf.mp hh
  rw [Submodule.mem_iInf] at hhY
  change resL p (Fin.last K, ρ) 0 h ∈ XSp p LL J M ρ
  have hresP : resL p (Fin.last K, ρ) 0 h ∈ Pol p r LL := resL_keep_supp (Fin.last K, ρ) 0 _ h hhP
  have key : ∀ j ≤ K, ∀ Mt : WithTop ℤ, ∀ x ∈ YCond p LL j Mt, resL p (Fin.last K, ρ) 0 x ∈ YCond p LL j Mt :=
    fun j hj Mt => ycond_keep LL j Mt (resL p (Fin.last K, ρ) 0)
      (fun c d x => resL_glAct LL j c d (Fin.last K, ρ) 0 (fun i hi =>
        ⟨fun h' => last_ne_of_lt i (by omega) (Prod.mk.inj h').1.symm,
          fun h' => last_ne_of_lt i (by omega) (Prod.mk.inj h').1.symm⟩) x)
      (resL_keep_supp (Fin.last K, ρ) 0 _)
  unfold XSp
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hresP, resL_free (Fin.last K, ρ) h⟩, ?_⟩
  rw [Submodule.mem_iInf]
  intro k
  split_ifs with hk
  · have h1 : h ∈ YCond p LL (K + 1) (M k) := by
      have := hhY k
      rw [ycond_min, min_eq_right hk] at this
      exact this
    refine Submodule.mem_inf.mpr ⟨key K le_rfl _ _ (condition_drop_holds p K r LL (M k) hv h hhP h1), ?_⟩
    have h0 : (0 : Fin r) ∈ (univ : Finset (Fin r)).erase ρ := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h'
      have := congrArg Fin.val h'
      simp at this
      omega
    obtain ⟨P, hP, -, -⟩ := hHP.1 (K + 1) le_rfl (univ.erase ρ) (Or.inr rfl)
      {la | ((la 0 : ℤ) : WithTop ℤ) ≤ M k} (fun la la' hl => by
        show (((la 0 : ℤ) : WithTop ℤ) ≤ M k) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ M k)
        rw [hl 0 h0])
    refine mem_typesLE_of_ycondC LL (K + 1) _ h0 (M k) P hP _ (Submodule.mem_inf.mpr ⟨?_, hresP⟩)
    refine ycondC_keep LL (K + 1) _ (M k) (resL p (Fin.last K, ρ) 0) (fun c hc d hd x =>
      resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 (fun i _ =>
        ⟨fun h' => (Finset.mem_erase.mp hc).1 (Prod.mk.inj h').2,
          fun h' => (Finset.mem_erase.mp hd).1 (Prod.mk.inj h').2⟩) x)
      (resL_keep_supp (Fin.last K, ρ) 0 _) h (ycond_le_ycondC LL (K + 1) _ (M k) h1)
  · exact key (J k) (by omega) _ _ (hhY k)

end Formalism.InvariantFactorPaths.L4

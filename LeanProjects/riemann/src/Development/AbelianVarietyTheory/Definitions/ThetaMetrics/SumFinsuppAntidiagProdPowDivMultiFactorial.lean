import Mathlib

open MvPolynomial Finset

noncomputable section

namespace GlobalTheory.MvPoly

variable {σ τ K L : Type*}

section Defs

variable [NormedCommRing K]

def l1Norm (P : MvPolynomial σ K) : ℝ := ∑ α ∈ P.support, ‖P.coeff α‖

def l2Norm (P : MvPolynomial σ K) : ℝ := √(∑ α ∈ P.support, ‖P.coeff α‖ ^ 2)

def supCoeff (P : MvPolynomial σ K) : ℝ := ((P.support.sup fun α ↦ ‖P.coeff α‖₊ : NNReal) : ℝ)

def multiFactorial (α : σ →₀ ℕ) : ℕ := α.prod fun _ n ↦ n.factorial

def fockNormSq (P : MvPolynomial σ K) : ℝ :=
  ∑ α ∈ P.support, (multiFactorial α : ℝ) * ‖P.coeff α‖ ^ 2

def fockInner {𝕜 : Type*} [RCLike 𝕜] (P Q : MvPolynomial σ 𝕜) : 𝕜 :=
  ∑ α ∈ P.support, (multiFactorial α : 𝕜) * (P.coeff α * starRingEnd 𝕜 (Q.coeff α))

def monomialsLE (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℕ) : Finset (σ →₀ ℕ) :=
  (range (d + 1)).biUnion fun k ↦ (univ : Finset σ).finsuppAntidiag k

end Defs

section L1

variable [NormedCommRing K] [NormedCommRing L]

theorem l1Norm_eq_sum_of_subset {P : MvPolynomial σ K} {s : Finset (σ →₀ ℕ)}
    (h : P.support ⊆ s) : l1Norm P = ∑ α ∈ s, ‖P.coeff α‖ :=
  sum_subset h fun α _ hα ↦ by rw [notMem_support_iff.mp hα, norm_zero]

theorem l1Norm_nonneg (P : MvPolynomial σ K) : 0 ≤ l1Norm P :=
  sum_nonneg fun _ _ ↦ norm_nonneg _

theorem sum_norm_coeff_le_l1Norm (P : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) :
    ∑ α ∈ s, ‖P.coeff α‖ ≤ l1Norm P := by
  classical
  rw [l1Norm_eq_sum_of_subset (s := P.support ∪ s) subset_union_left]
  exact sum_le_sum_of_subset_of_nonneg subset_union_right fun _ _ _ ↦ norm_nonneg _

theorem norm_coeff_le_l1Norm (P : MvPolynomial σ K) (α : σ →₀ ℕ) : ‖P.coeff α‖ ≤ l1Norm P := by
  simpa using sum_norm_coeff_le_l1Norm P {α}

@[simp] theorem l1Norm_zero : l1Norm (0 : MvPolynomial σ K) = 0 := by simp [l1Norm]

@[simp] theorem l1Norm_eq_zero {P : MvPolynomial σ K} : l1Norm P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ l1Norm_zero⟩
  ext α
  simpa using norm_le_zero_iff.mp (h ▸ norm_coeff_le_l1Norm P α)

@[simp] theorem l1Norm_monomial (α : σ →₀ ℕ) (c : K) : l1Norm (monomial α c) = ‖c‖ := by
  classical
  rw [l1Norm_eq_sum_of_subset (s := {α}) support_monomial_subset]
  simp

@[simp] theorem l1Norm_C (c : K) : l1Norm (C c : MvPolynomial σ K) = ‖c‖ := l1Norm_monomial 0 c

@[simp] theorem l1Norm_one [NormOneClass K] : l1Norm (1 : MvPolynomial σ K) = 1 := by
  rw [← C_1, l1Norm_C, norm_one]

@[simp] theorem l1Norm_X [NormOneClass K] (i : σ) : l1Norm (X i : MvPolynomial σ K) = 1 := by
  rw [X, l1Norm_monomial, norm_one]

@[simp] theorem l1Norm_neg (P : MvPolynomial σ K) : l1Norm (-P) = l1Norm P := by
  simp [l1Norm]

theorem l1Norm_add_le (P Q : MvPolynomial σ K) : l1Norm (P + Q) ≤ l1Norm P + l1Norm Q := by
  classical
  rw [l1Norm_eq_sum_of_subset (s := P.support ∪ Q.support) support_add,
    l1Norm_eq_sum_of_subset (s := P.support ∪ Q.support) subset_union_left,
    l1Norm_eq_sum_of_subset (s := P.support ∪ Q.support) subset_union_right, ← sum_add_distrib]
  exact sum_le_sum fun α _ ↦ by rw [coeff_add]; exact norm_add_le _ _

theorem l1Norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) :=
  Finset.le_sum_of_subadditive l1Norm l1Norm_zero.le l1Norm_add_le s f

theorem l1Norm_mul_le (P Q : MvPolynomial σ K) : l1Norm (P * Q) ≤ l1Norm P * l1Norm Q := by
  conv_lhs => rw [P.as_sum, Q.as_sum, sum_mul_sum]
  refine (l1Norm_sum_le _ _).trans ?_
  rw [l1Norm, l1Norm, sum_mul_sum]
  refine sum_le_sum fun α _ ↦ (l1Norm_sum_le _ _).trans (sum_le_sum fun β _ ↦ ?_)
  rw [monomial_mul, l1Norm_monomial]
  exact norm_mul_le _ _

def l1RingNorm (σ K : Type*) [NormedCommRing K] : RingNorm (MvPolynomial σ K) where
  toFun := l1Norm
  map_zero' := l1Norm_zero
  add_le' := l1Norm_add_le
  neg' := l1Norm_neg
  mul_le' := l1Norm_mul_le
  eq_zero_of_map_eq_zero' _ := l1Norm_eq_zero.mp

@[simp] theorem l1RingNorm_apply (P : MvPolynomial σ K) : l1RingNorm σ K P = l1Norm P := rfl

def l1RingSeminorm (σ K : Type*) [NormedCommRing K] : RingSeminorm (MvPolynomial σ K) :=
  (l1RingNorm σ K).toRingSeminorm

@[simp] theorem l1RingSeminorm_apply (P : MvPolynomial σ K) :
    l1RingSeminorm σ K P = l1Norm P := rfl

theorem l1Norm_smul_le (c : K) (P : MvPolynomial σ K) : l1Norm (c • P) ≤ ‖c‖ * l1Norm P := by
  rw [smul_eq_C_mul, ← l1Norm_C (σ := σ)]; exact l1Norm_mul_le _ _

theorem l1Norm_prod_le [NormOneClass K] {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    l1Norm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (l1Norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (l1Norm_nonneg _))

theorem l1Norm_pow_le [NormOneClass K] (P : MvPolynomial σ K) (n : ℕ) :
    l1Norm (P ^ n) ≤ l1Norm P ^ n := by
  simpa using l1Norm_prod_le (range n) fun _ ↦ P

theorem l1Norm_prod_pow_le [NormOneClass K] {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K) (c : ι → ℕ) (B : ι → ℝ) (h : ∀ i ∈ s, l1Norm (f i) ≤ B i) :
    l1Norm (∏ i ∈ s, f i ^ c i) ≤ ∏ i ∈ s, B i ^ c i :=
  (l1Norm_prod_le _ _).trans <| prod_le_prod (fun _ _ ↦ l1Norm_nonneg _) fun i hi ↦
    (l1Norm_pow_le _ _).trans (pow_le_pow_left₀ (l1Norm_nonneg _) (h i hi) _)

theorem l1Norm_rename_of_injective {f : σ → τ} (hf : Function.Injective f)
    (P : MvPolynomial σ K) : l1Norm (rename f P) = l1Norm P := by
  classical
  rw [l1Norm, support_rename_of_injective hf,
    sum_image fun _ _ _ _ h ↦ Finsupp.mapDomain_injective hf h, l1Norm]
  simp [coeff_rename_mapDomain f hf]

theorem l1Norm_map {R : Type*} [CommSemiring R] (φ : R →+* K) (P : MvPolynomial σ R) :
    l1Norm (map φ P) = ∑ α ∈ P.support, ‖φ (P.coeff α)‖ := by
  rw [l1Norm_eq_sum_of_subset (support_map_subset φ P)]
  simp [coeff_map]

end L1

section Linear

variable [NormedCommRing K]

theorem sum_le_sqrt_card_mul_sqrt_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, f i ≤ √(#s) * √(∑ i ∈ s, f i ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.le_sqrt_of_sq_le sq_sum_le_card_mul_sum_sq

theorem l1Norm_linearForm_le_sum {ι : Type*} (s : Finset ι) (v : ι → σ) (e : ι → K) :
    l1Norm (∑ k ∈ s, C (e k) * X (v k) : MvPolynomial σ K) ≤ ∑ k ∈ s, ‖e k‖ := by
  refine (l1Norm_sum_le _ _).trans_eq (sum_congr rfl fun k _ ↦ ?_)
  rw [C_mul_X_eq_monomial, l1Norm_monomial]

theorem l1Norm_linearForm_eq_sum {ι : Type*} (s : Finset ι) {v : ι → σ}
    (hv : Function.Injective v) (e : ι → K) :
    l1Norm (∑ k ∈ s, C (e k) * X (v k) : MvPolynomial σ K) = ∑ k ∈ s, ‖e k‖ := by
  classical
  refine (l1Norm_linearForm_le_sum s v e).antisymm ?_
  have hinj : Function.Injective fun k ↦ (Finsupp.single (v k) 1 : σ →₀ ℕ) :=
    fun a b h ↦ hv (Finsupp.single_left_injective one_ne_zero h)
  refine le_trans (le_of_eq ?_) (sum_norm_coeff_le_l1Norm _ (s.image fun k ↦ .single (v k) 1))
  rw [sum_image fun a _ b _ h ↦ hinj h]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [coeff_sum, sum_eq_single k]
  · simp [C_mul_X_eq_monomial]
  · intro b _ hb
    rw [C_mul_X_eq_monomial, coeff_monomial, if_neg fun h ↦ hb (hinj h)]
  · exact fun h ↦ (h hk).elim

theorem l1Norm_linearForm_le {ι : Type*} [Fintype ι] (v : ι → σ) (e : ι → K) :
    l1Norm (∑ k, C (e k) * X (v k) : MvPolynomial σ K) ≤
      √(Fintype.card ι) * √(∑ k, ‖e k‖ ^ 2) :=
  (l1Norm_linearForm_le_sum _ v e).trans (sum_le_sqrt_card_mul_sqrt_sum_sq _ _)

theorem l1Norm_det_le [NormOneClass K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ K)) {R : ℝ} (h : ∀ a b, l1Norm (M a b) ≤ R) :
    l1Norm M.det ≤ (Fintype.card ι).factorial * R ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine (l1Norm_sum_le _ _).trans ?_
  rw [← Fintype.card_perm, ← nsmul_eq_mul, ← card_univ (α := Equiv.Perm ι)]
  refine sum_le_card_nsmul _ _ _ fun π _ ↦ ?_
  have h1 : l1Norm (Equiv.Perm.sign π • ∏ i, M (π i) i) = l1Norm (∏ i, M (π i) i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  rw [h1]
  refine (l1Norm_prod_le _ _).trans ?_
  rw [← card_univ, ← prod_const]
  exact prod_le_prod (fun _ _ ↦ l1Norm_nonneg _) fun _ _ ↦ h _ _

theorem factorial_mul_pow_le (i : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (i.factorial : ℝ) * R ^ i ≤ (i * R) ^ i := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le_pow i) (pow_nonneg hR _)

theorem l1Norm_det_le_pow [NormOneClass K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ K)) {R : ℝ} (h : ∀ a b, l1Norm (M a b) ≤ R) :
    l1Norm M.det ≤ (Fintype.card ι * R) ^ Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a⟩⟩
  · simp
  · exact (l1Norm_det_le M h).trans (factorial_mul_pow_le _ ((l1Norm_nonneg _).trans (h a a)))

end Linear

section Eval

variable [NormedCommRing K]

theorem degree_le_totalDegree {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {α : σ →₀ ℕ}
    (h : α ∈ P.support) : α.degree ≤ P.totalDegree := le_totalDegree h

theorem l1Norm_bind_le_sum_norm_coeff_mul_pow_degree [NormOneClass K] (f : σ → MvPolynomial τ K) (P : MvPolynomial σ K)
    {R : ℝ} (h : ∀ i, l1Norm (f i) ≤ R) :
    l1Norm (bind₁ f P) ≤ ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine (l1Norm_sum_le _ _).trans (sum_le_sum fun α _ ↦ ?_)
  rw [bind₁_monomial]
  refine (l1Norm_mul_le _ _).trans ?_
  rw [l1Norm_C, Finsupp.degree_apply, ← prod_pow_eq_pow_sum]
  exact mul_le_mul_of_nonneg_left (l1Norm_prod_pow_le _ _ _ _ fun i _ ↦ h i) (norm_nonneg _)

theorem sum_norm_coeff_mul_pow_le (P : MvPolynomial σ K) {R : ℝ} (hR : 0 ≤ R) {d : ℕ}
    (hd : P.totalDegree ≤ d) :
    ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree ≤ l1Norm P * max 1 R ^ d := by
  rw [l1Norm, sum_mul]
  refine sum_le_sum fun α hα ↦ mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (pow_le_pow_left₀ hR (le_max_right 1 R) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) ((degree_le_totalDegree hα).trans hd))

theorem sum_norm_coeff_mul_pow_of_isHomogeneous {P : MvPolynomial σ K} {d : ℕ}
    (hP : P.IsHomogeneous d) (R : ℝ) :
    ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree = l1Norm P * R ^ d := by
  rw [l1Norm, sum_mul]
  refine sum_congr rfl fun α hα ↦ ?_
  rw [hP.degree_eq_sum_deg_support hα, Finsupp.degree_apply]

theorem l1Norm_bind_le_mul_pow_of_isHomogeneous [NormOneClass K] (f : σ → MvPolynomial τ K)
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) {R : ℝ}
    (h : ∀ i, l1Norm (f i) ≤ R) : l1Norm (bind₁ f P) ≤ l1Norm P * R ^ d :=
  (l1Norm_bind_le_sum_norm_coeff_mul_pow_degree f P h).trans_eq (sum_norm_coeff_mul_pow_of_isHomogeneous hP R)

theorem norm_eval_le_sum [NormOneClass K] (x : σ → K) (P : MvPolynomial σ K) {R : ℝ}
    (h : ∀ i, ‖x i‖ ≤ R) : ‖eval x P‖ ≤ ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree := by
  rw [eval_eq]
  refine norm_sum_le_of_le _ fun α _ ↦ (norm_mul_le _ _).trans ?_
  rw [Finsupp.degree_apply, ← prod_pow_eq_pow_sum]
  refine mul_le_mul_of_nonneg_left ((Finset.norm_prod_le _ _).trans ?_) (norm_nonneg _)
  exact prod_le_prod (fun _ _ ↦ norm_nonneg _) fun i _ ↦
    (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (h i) _)

theorem norm_eval_le_of_le [NormOneClass K] (x : σ → K) (P : MvPolynomial σ K) {R : ℝ}
    (h : ∀ i, ‖x i‖ ≤ R) {d : ℕ} (hd : P.totalDegree ≤ d) :
    ‖eval x P‖ ≤ l1Norm P * max 1 R ^ d := by
  have := (norm_eval_le_sum x P fun i ↦ (h i).trans (le_max_right 1 R)).trans
    (sum_norm_coeff_mul_pow_le P (zero_le_one.trans (le_max_left 1 R)) hd)
  rwa [← max_assoc, max_self] at this

theorem norm_eval_le [NormOneClass K] [Fintype σ] (x : σ → K) (P : MvPolynomial σ K) :
    ‖eval x P‖ ≤ l1Norm P * max 1 ‖x‖ ^ P.totalDegree :=
  norm_eval_le_of_le x P (norm_le_pi_norm x) le_rfl

end Eval

section Count

variable [Fintype σ] [DecidableEq σ]

@[simp] theorem mem_monomialsLE {d : ℕ} {α : σ →₀ ℕ} : α ∈ monomialsLE σ d ↔ α.degree ≤ d := by
  simp [monomialsLE, mem_finsuppAntidiag, Finsupp.degree_eq_sum]

theorem card_monomialsLE (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℕ) :
    #(monomialsLE σ d) = (Fintype.card σ + d).choose d := by
  rw [monomialsLE, card_biUnion]
  · simp_rw [card_finsuppAntidiag_nat_eq_multichoose]
    rw [Nat.sum_range_multichoose, card_univ, add_comm d]
    exact Nat.choose_symm_add
  · intro a _ b _ hab
    refine disjoint_left.mpr fun α ha hb ↦ hab ?_
    rw [mem_finsuppAntidiag] at ha hb
    exact ha.1.symm.trans hb.1

theorem choose_add_le_one_add_pow (N d : ℕ) : (N + d).choose d ≤ (1 + d) ^ N := by
  rw [← Nat.choose_symm_add, add_comm N d, add_comm 1 d]
  exact Nat.choose_add_le_add_one_pow d N

theorem support_subset_monomialsLE {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ} :
    P.support ⊆ monomialsLE σ d ↔ P.totalDegree ≤ d :=
  ⟨fun h ↦ Finset.sup_le fun _ hα ↦ mem_monomialsLE.mp (h hα),
    fun h _ hα ↦ mem_monomialsLE.mpr ((degree_le_totalDegree hα).trans h)⟩

omit [DecidableEq σ] in

theorem card_support_le_choose {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ}
    (h : P.totalDegree ≤ d) : #P.support ≤ (Fintype.card σ + d).choose d := by
  classical
  exact card_monomialsLE σ d ▸ card_le_card (support_subset_monomialsLE.mpr h)

omit [DecidableEq σ] in

theorem ncard_setOf_degree_le (d : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ d}.ncard = (Fintype.card σ + d).choose d := by
  classical
  rw [← card_monomialsLE, ← Set.ncard_coe_finset]
  congr 1
  ext α
  simp

omit [DecidableEq σ] in

theorem finrank_restrictTotalDegree (R : Type*) [CommRing R] [Nontrivial R] (d : ℕ) :
    Module.finrank R (restrictTotalDegree σ R d) = (Fintype.card σ + d).choose d := by
  rw [← ncard_setOf_degree_le, ← Nat.card_coe_set_eq]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport R _)

end Count

section L2

variable [NormedCommRing K] [NormedCommRing L]

theorem l2Norm_nonneg (P : MvPolynomial σ K) : 0 ≤ l2Norm P := Real.sqrt_nonneg _

theorem fubiniStudy_l2Norm_sq_eq (P : MvPolynomial σ K) : l2Norm P ^ 2 = ∑ α ∈ P.support, ‖P.coeff α‖ ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun _ _ ↦ sq_nonneg _)

theorem l2Norm_eq_sqrt_sum_of_subset {P : MvPolynomial σ K} {s : Finset (σ →₀ ℕ)}
    (h : P.support ⊆ s) : l2Norm P = √(∑ α ∈ s, ‖P.coeff α‖ ^ 2) := by
  rw [l2Norm, sum_subset h fun α _ hα ↦ by simp [notMem_support_iff.mp hα]]

@[simp] theorem l2Norm_zero : l2Norm (0 : MvPolynomial σ K) = 0 := by simp [l2Norm]

@[simp] theorem l2Norm_monomial (α : σ →₀ ℕ) (c : K) : l2Norm (monomial α c) = ‖c‖ := by
  classical
  rw [l2Norm_eq_sqrt_sum_of_subset (s := {α}) support_monomial_subset]
  simp

@[simp] theorem l2Norm_neg (P : MvPolynomial σ K) : l2Norm (-P) = l2Norm P := by
  simp [l2Norm]

theorem vectorL2Norm_const_mul [NormMulClass K] (c : K) (P : MvPolynomial σ K) :
    l2Norm (c • P) = ‖c‖ * l2Norm P := by
  rw [l2Norm_eq_sqrt_sum_of_subset (s := P.support) support_smul, l2Norm,
    ← Real.sqrt_sq (norm_nonneg c), ← Real.sqrt_mul (sq_nonneg _), mul_sum]
  simp [mul_pow]

theorem norm_coeff_le_l2Norm (P : MvPolynomial σ K) (α : σ →₀ ℕ) : ‖P.coeff α‖ ≤ l2Norm P := by
  classical
  rw [l2Norm_eq_sqrt_sum_of_subset (s := insert α P.support) (subset_insert _ _)]
  exact Real.le_sqrt_of_sq_le
    (single_le_sum (f := fun β ↦ ‖P.coeff β‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_insert_self _ _))

@[simp] theorem l2Norm_eq_zero {P : MvPolynomial σ K} : l2Norm P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ l2Norm_zero⟩
  ext α
  simpa using norm_le_zero_iff.mp (h ▸ norm_coeff_le_l2Norm P α)

theorem l2Norm_le_l1Norm (P : MvPolynomial σ K) : l2Norm P ≤ l1Norm P :=
  Real.sqrt_le_iff.mpr ⟨l1Norm_nonneg P, sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ norm_nonneg _⟩

theorem l1Norm_le_sqrt_card_mul_l2Norm (P : MvPolynomial σ K) :
    l1Norm P ≤ √(#P.support) * l2Norm P :=
  sum_le_sqrt_card_mul_sqrt_sum_sq _ _

theorem l1Norm_le_sqrt_choose_mul_l2Norm [Fintype σ] {P : MvPolynomial σ K} {d : ℕ}
    (h : P.totalDegree ≤ d) : l1Norm P ≤ √((Fintype.card σ + d).choose d) * l2Norm P :=
  (l1Norm_le_sqrt_card_mul_l2Norm P).trans <| mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (by exact_mod_cast card_support_le_choose h)) (l2Norm_nonneg P)

theorem supCoeff_nonneg (P : MvPolynomial σ K) : 0 ≤ supCoeff P := NNReal.coe_nonneg _

theorem norm_coeff_le_supCoeff (P : MvPolynomial σ K) (α : σ →₀ ℕ) :
    ‖P.coeff α‖ ≤ supCoeff P := by
  by_cases h : α ∈ P.support
  · exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun α ↦ ‖P.coeff α‖₊) h)
  · rw [notMem_support_iff.mp h, norm_zero]; exact supCoeff_nonneg P

theorem supCoeff_le_iff {P : MvPolynomial σ K} {B : ℝ} (hB : 0 ≤ B) :
    supCoeff P ≤ B ↔ ∀ α, ‖P.coeff α‖ ≤ B := by
  refine ⟨fun h α ↦ (norm_coeff_le_supCoeff P α).trans h, fun h ↦ ?_⟩
  lift B to NNReal using hB
  exact NNReal.coe_le_coe.mpr (Finset.sup_le fun α _ ↦ h α)

@[simp] theorem supCoeff_zero : supCoeff (0 : MvPolynomial σ K) = 0 := by simp [supCoeff]

@[simp] theorem supCoeff_eq_zero {P : MvPolynomial σ K} : supCoeff P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ supCoeff_zero⟩
  ext α
  simpa using norm_le_zero_iff.mp (h ▸ norm_coeff_le_supCoeff P α)

@[simp] theorem supCoeff_monomial (α : σ →₀ ℕ) (c : K) : supCoeff (monomial α c) = ‖c‖ := by
  classical
  refine le_antisymm ((supCoeff_le_iff (norm_nonneg c)).mpr fun β ↦ ?_) ?_
  · rw [coeff_monomial]; split_ifs <;> simp
  · simpa using norm_coeff_le_supCoeff (monomial α c) α

end L2

section Fock

theorem multiFactorial_pos (α : σ →₀ ℕ) : 0 < multiFactorial α :=
  prod_pos fun _ _ ↦ Nat.factorial_pos _

@[simp] theorem multiFactorial_zero : multiFactorial (0 : σ →₀ ℕ) = 1 := by simp [multiFactorial]

@[simp] theorem multiFactorial_single (i : σ) (n : ℕ) :
    multiFactorial (Finsupp.single i n) = n.factorial :=
  Finsupp.prod_single_index rfl

theorem multiFactorial_add_single (α : σ →₀ ℕ) (i : σ) :
    multiFactorial (α + Finsupp.single i 1) = (α i + 1) * multiFactorial α := by
  classical
  have h1 : ∀ β : σ →₀ ℕ, β.support ⊆ insert i α.support →
      multiFactorial β = (β i).factorial * ∏ j ∈ (insert i α.support).erase i, (β j).factorial :=
    fun β hβ ↦ by
      rw [multiFactorial, Finsupp.prod_of_support_subset β hβ _ fun _ _ ↦ rfl,
        mul_prod_erase _ (fun j ↦ (β j).factorial) (mem_insert_self _ _)]
  rw [h1 α (subset_insert _ _), h1 _ (Finsupp.support_add.trans ?_), ← mul_assoc]
  · congr 1
    · simp [Nat.factorial_succ]
    · refine prod_congr rfl fun j hj ↦ ?_
      simp [Finsupp.single_eq_of_ne (ne_of_mem_erase hj)]
  · exact union_subset (subset_insert _ _)
      (Finsupp.support_single_subset.trans (by simp))

variable [NormedCommRing K] [NormedCommRing L]

theorem fockNormSq_eq_sum_of_subset {P : MvPolynomial σ K} {s : Finset (σ →₀ ℕ)}
    (h : P.support ⊆ s) : fockNormSq P = ∑ α ∈ s, (multiFactorial α : ℝ) * ‖P.coeff α‖ ^ 2 :=
  sum_subset h fun α _ hα ↦ by simp [notMem_support_iff.mp hα]

theorem fockNormSq_nonneg (P : MvPolynomial σ K) : 0 ≤ fockNormSq P :=
  sum_nonneg fun _ _ ↦ by positivity

@[simp] theorem fockNormSq_zero : fockNormSq (0 : MvPolynomial σ K) = 0 := by simp [fockNormSq]

@[simp] theorem fockNormSq_monomial (α : σ →₀ ℕ) (c : K) :
    fockNormSq (monomial α c) = multiFactorial α * ‖c‖ ^ 2 := by
  classical
  rw [fockNormSq_eq_sum_of_subset (s := {α}) support_monomial_subset]
  simp

theorem l2Norm_sq_le_fockNormSq (P : MvPolynomial σ K) : l2Norm P ^ 2 ≤ fockNormSq P := by
  rw [fubiniStudy_l2Norm_sq_eq]
  exact sum_le_sum fun α _ ↦ le_mul_of_one_le_left (sq_nonneg _)
    (by exact_mod_cast multiFactorial_pos α)

@[simp] theorem fockNormSq_eq_zero {P : MvPolynomial σ K} : fockNormSq P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ l2Norm_eq_zero.mp ?_, fun h ↦ h ▸ fockNormSq_zero⟩
  exact pow_eq_zero_iff two_ne_zero |>.mp
    (le_antisymm (h ▸ l2Norm_sq_le_fockNormSq P) (sq_nonneg _))

variable {𝕜 : Type*} [RCLike 𝕜]

theorem fockInner_eq_sum_of_subset_left {P : MvPolynomial σ 𝕜} (Q : MvPolynomial σ 𝕜)
    {s : Finset (σ →₀ ℕ)} (h : P.support ⊆ s) : fockInner P Q =
      ∑ α ∈ s, (multiFactorial α : 𝕜) * (P.coeff α * starRingEnd 𝕜 (Q.coeff α)) :=
  sum_subset h fun α _ hα ↦ by simp [notMem_support_iff.mp hα]

theorem fockInner_eq_sum_of_subset_right (P : MvPolynomial σ 𝕜) {Q : MvPolynomial σ 𝕜}
    {s : Finset (σ →₀ ℕ)} (h : Q.support ⊆ s) : fockInner P Q =
      ∑ α ∈ s, (multiFactorial α : 𝕜) * (P.coeff α * starRingEnd 𝕜 (Q.coeff α)) := by
  classical
  rw [fockInner_eq_sum_of_subset_left Q (s := P.support ∪ s) subset_union_left]
  exact (sum_subset subset_union_right fun α _ hα ↦ by
    simp [notMem_support_iff.mp fun h' ↦ hα (h h')]).symm

theorem fockInner_conj_symm (P Q : MvPolynomial σ 𝕜) :
    starRingEnd 𝕜 (fockInner P Q) = fockInner Q P := by
  rw [fockInner_eq_sum_of_subset_right Q (subset_refl P.support), fockInner, map_sum]
  exact sum_congr rfl fun α _ ↦ by simp [mul_comm]

theorem fockInner_add_left (P P' Q : MvPolynomial σ 𝕜) :
    fockInner (P + P') Q = fockInner P Q + fockInner P' Q := by
  simp only [fockInner_eq_sum_of_subset_right _ (subset_refl Q.support), coeff_add, add_mul,
    mul_add, sum_add_distrib]

theorem fockInner_smul_left (c : 𝕜) (P Q : MvPolynomial σ 𝕜) :
    fockInner (c • P) Q = c * fockInner P Q := by
  simp only [fockInner_eq_sum_of_subset_right _ (subset_refl Q.support), mul_sum]
  exact sum_congr rfl fun α _ ↦ by rw [coeff_smul, smul_eq_mul]; ring

theorem fockInner_add_right (P Q Q' : MvPolynomial σ 𝕜) :
    fockInner P (Q + Q') = fockInner P Q + fockInner P Q' := by
  simp only [fockInner, coeff_add, map_add, mul_add, sum_add_distrib]

theorem fockInner_smul_right (c : 𝕜) (P Q : MvPolynomial σ 𝕜) :
    fockInner P (c • Q) = starRingEnd 𝕜 c * fockInner P Q := by
  simp only [fockInner, mul_sum]
  exact sum_congr rfl fun α _ ↦ by rw [coeff_smul, smul_eq_mul, map_mul]; ring

def fockInnerₛₗ (σ 𝕜 : Type*) [RCLike 𝕜] :
    MvPolynomial σ 𝕜 →ₗ[𝕜] MvPolynomial σ 𝕜 →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd 𝕜) fockInner fockInner_add_left
    fockInner_smul_left fockInner_add_right fockInner_smul_right

@[simp] theorem fockInnerₛₗ_apply (P Q : MvPolynomial σ 𝕜) :
    fockInnerₛₗ σ 𝕜 P Q = fockInner P Q := rfl

theorem fockInner_self (P : MvPolynomial σ 𝕜) : fockInner P P = (fockNormSq P : 𝕜) := by
  simp [fockInner, fockNormSq, RCLike.mul_conj]

theorem fockInner_monomial_left (α : σ →₀ ℕ) (c : 𝕜) (Q : MvPolynomial σ 𝕜) :
    fockInner (monomial α c) Q = multiFactorial α * (c * starRingEnd 𝕜 (Q.coeff α)) := by
  classical
  rw [fockInner_eq_sum_of_subset_left Q (s := {α}) support_monomial_subset]
  simp

theorem fockInner_monomial_right (P : MvPolynomial σ 𝕜) (α : σ →₀ ℕ) (c : 𝕜) :
    fockInner P (monomial α c) = multiFactorial α * (P.coeff α * starRingEnd 𝕜 c) := by
  classical
  rw [fockInner_eq_sum_of_subset_right P (s := {α}) support_monomial_subset]
  simp

theorem fockInner_X_mul_left (i : σ) (P Q : MvPolynomial σ 𝕜) :
    fockInner (X i * P) Q = fockInner P (pderiv i Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul, one_mul, fockInner_monomial_left, fockInner_monomial_left, coeff_pderiv,
      add_comm _ α, multiFactorial_add_single]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul, map_add, map_natCast, map_one]
    ring
  | add P P' h h' => rw [mul_add, fockInner_add_left, fockInner_add_left, h, h']

theorem fockInner_pderiv_left (i : σ) (P Q : MvPolynomial σ 𝕜) :
    fockInner (pderiv i P) Q = fockInner P (X i * Q) := by
  rw [← fockInner_conj_symm, ← fockInner_X_mul_left, fockInner_conj_symm]

end Fock

example : l1Norm (C 3 * X 0 + C (-4) * X 1 : MvPolynomial (Fin 2) ℂ) = 7 := by
  have := l1Norm_linearForm_eq_sum (K := ℂ) univ (v := id) Function.injective_id ![3, -4]
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, id] at this
  rw [this]
  norm_num

example : l2Norm (monomial 0 3 + monomial (Finsupp.single 0 1) 4 : MvPolynomial (Fin 1) ℂ) = 5 ∧
    supCoeff (monomial 0 3 + monomial (Finsupp.single 0 1) 4 : MvPolynomial (Fin 1) ℂ) = 4 := by
  have hne : (Finsupp.single 0 1 : Fin 1 →₀ ℕ) ≠ 0 := by simp
  constructor
  · rw [l2Norm_eq_sqrt_sum_of_subset (s := {0, Finsupp.single 0 1})
      (support_add.trans (union_subset (support_monomial_subset.trans (by simp))
        (support_monomial_subset.trans (by simp)))), sum_pair hne.symm]
    simp only [coeff_add, coeff_monomial, hne, hne.symm, if_true, if_false]
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  · refine le_antisymm ((supCoeff_le_iff (by norm_num)).mpr fun β ↦ ?_) ?_
    · simp only [coeff_add, coeff_monomial]
      split_ifs with h1 h2
      · exact (hne (h2.trans h1.symm)).elim
      all_goals norm_num
    · refine le_trans (le_of_eq ?_) (norm_coeff_le_supCoeff _ (Finsupp.single 0 1))
      simp [coeff_monomial, hne.symm]

example : fockNormSq (X 0 ^ 3 : MvPolynomial (Fin 2) ℂ) = 6 := by
  rw [X_pow_eq_monomial, fockNormSq_monomial, multiFactorial_single]
  norm_num [Nat.factorial]

example : fockInner (1 : MvPolynomial (Fin 1) ℂ) (C Complex.I) = -Complex.I := by
  rw [C_apply, fockInner_monomial_right]
  simp

example : #(monomialsLE (Fin 2) 2) = 6 := by
  rw [card_monomialsLE]; decide

end GlobalTheory.MvPoly

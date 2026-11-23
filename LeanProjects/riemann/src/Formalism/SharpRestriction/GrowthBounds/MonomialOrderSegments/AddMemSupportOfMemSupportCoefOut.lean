import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section Lord

variable {R : Type} [Semiring R]

theorem le_lord_iff (n : WithTop ℤ) (f : LaurentPolynomial R) :
    n ≤ lord f ↔ ∀ k : ℤ, f.coeff k ≠ 0 → n ≤ (k : WithTop ℤ) := by
  unfold lord
  rw [Finset.le_min_iff]
  simp only [Finsupp.mem_support_iff]

theorem lord_zero : lord (0 : LaurentPolynomial R) = ⊤ := by
  rw [eq_top_iff, le_lord_iff]
  intro k hk
  exact absurd rfl hk

theorem le_lord_add {n : WithTop ℤ} {f g : LaurentPolynomial R} (hf : n ≤ lord f) (hg : n ≤ lord g) :
    n ≤ lord (f + g) := by
  rw [le_lord_iff] at *
  intro k hk
  by_cases h1 : f.coeff k = 0
  · apply hg k
    intro h2
    apply hk
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h1, h2, add_zero]
  · exact hf k h1

theorem le_lord_sum {ι : Type} {n : WithTop ℤ} (s : Finset ι) (f : ι → LaurentPolynomial R)
    (h : ∀ i ∈ s, n ≤ lord (f i)) : n ≤ lord (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lord_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_lord_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem le_lord_mul {m n : WithTop ℤ} {f g : LaurentPolynomial R} (hf : m ≤ lord f) (hg : n ≤ lord g) :
    m + n ≤ lord (f * g) := by
  classical
  rw [le_lord_iff] at *
  intro k hk
  have hk' : k ∈ (f * g).coeff.support := Finsupp.mem_support_iff.mpr hk
  have := AddMonoidAlgebra.support_coeff_mul_subset f g hk'
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp this
  have h1 := hf a (Finsupp.mem_support_iff.mp ha)
  have h2 := hg b (Finsupp.mem_support_iff.mp hb)
  rw [WithTop.coe_add]
  exact add_le_add h1 h2

theorem lord_C_nonneg (a : R) : (0 : WithTop ℤ) ≤ lord (LaurentPolynomial.C a) := by
  rw [le_lord_iff]
  intro k hk
  rw [LaurentPolynomial.C_apply] at hk
  split_ifs at hk with h
  · rw [h]; exact le_refl _
  · exact absurd rfl hk

end Lord

section Pge

variable {R : Type} [CommSemiring R] {σ : Type}

def pge (n : WithTop ℤ) (G : MvPolynomial σ (LaurentPolynomial R)) : Prop :=
  ∀ β, n ≤ lord (G.coeff β)

theorem pge_zero (n : WithTop ℤ) : pge n (0 : MvPolynomial σ (LaurentPolynomial R)) := by
  intro β; rw [coeff_zero, lord_zero]; exact le_top

theorem pge_add {n : WithTop ℤ} {F G : MvPolynomial σ (LaurentPolynomial R)} (hF : pge n F)
    (hG : pge n G) : pge n (F + G) := by
  intro β; rw [coeff_add]; exact le_lord_add (hF β) (hG β)

theorem pge_sum {ι : Type} {n : WithTop ℤ} (s : Finset ι)
    (f : ι → MvPolynomial σ (LaurentPolynomial R)) (h : ∀ i ∈ s, pge n (f i)) :
    pge n (∑ i ∈ s, f i) := by
  intro β; rw [coeff_sum]; exact le_lord_sum s _ fun i hi => h i hi β

theorem pge_mul {m n : WithTop ℤ} {F G : MvPolynomial σ (LaurentPolynomial R)} (hF : pge m F)
    (hG : pge n G) : pge (m + n) (F * G) := by
  classical
  intro β; rw [coeff_mul]
  exact le_lord_sum _ _ fun x _ => le_lord_mul (hF x.1) (hG x.2)

theorem pge_mono {m n : WithTop ℤ} (h : m ≤ n) {F : MvPolynomial σ (LaurentPolynomial R)}
    (hF : pge n F) : pge m F := fun β => h.trans (hF β)

theorem pge_iff_inf (n : WithTop ℤ) (G : MvPolynomial σ (LaurentPolynomial R)) :
    (n ≤ G.support.inf fun β => lord (G.coeff β)) ↔ pge n G := by
  rw [Finset.le_inf_iff]
  constructor
  · intro h β
    by_cases hβ : β ∈ G.support
    · exact h β hβ
    · rw [notMem_support_iff.mp hβ, lord_zero]; exact le_top
  · intro h β _; exact h β

end Pge

section Basic

variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)

abbrev subV : MvPolynomial (L × Fin r) K →+* MvPolynomial (L × Fin r) (LauF K r) :=
  substS (lauι K r) sg S (hMat K r) (hInvT K r)

theorem le_valS_iff (n : WithTop ℤ) (F : MvPolynomial (L × Fin r) K) :
    n ≤ valS sg S F ↔ ∀ β, n ≤ lord ((subV sg S F).coeff β) := by
  unfold valS
  exact pge_iff_inf n _

theorem le_valS_iff_pge (n : WithTop ℤ) (F : MvPolynomial (L × Fin r) K) :
    n ≤ valS sg S F ↔ pge n (subV sg S F) := le_valS_iff sg S n F

theorem pge_valS (F : MvPolynomial (L × Fin r) K) : pge (valS sg S F) (subV sg S F) :=
  (le_valS_iff_pge sg S _ F).mp le_rfl

theorem valS_zero : valS sg S (0 : MvPolynomial (L × Fin r) K) = ⊤ := by
  rw [eq_top_iff, le_valS_iff_pge, map_zero]; exact pge_zero _

theorem valS_add_le (F G : MvPolynomial (L × Fin r) K) :
    min (valS sg S F) (valS sg S G) ≤ valS sg S (F + G) := by
  rw [le_valS_iff_pge, map_add]
  exact pge_add (pge_mono (min_le_left _ _) (pge_valS sg S F))
    (pge_mono (min_le_right _ _) (pge_valS sg S G))

theorem valS_sum_le {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) K) (n : WithTop ℤ)
    (h : ∀ i ∈ s, n ≤ valS sg S (f i)) : n ≤ valS sg S (∑ i ∈ s, f i) := by
  rw [le_valS_iff_pge, map_sum]
  exact pge_sum s _ fun i hi => (le_valS_iff_pge sg S n _).mp (h i hi)

theorem valS_mul_le (F G : MvPolynomial (L × Fin r) K) :
    valS sg S F + valS sg S G ≤ valS sg S (F * G) := by
  rw [le_valS_iff_pge, map_mul]
  exact pge_mul (pge_valS sg S F) (pge_valS sg S G)

theorem subV_C (a : K) : subV sg S (C a : MvPolynomial (L × Fin r) K) = C (lauι K r a) := by
  simp [substS]

theorem valS_C_nonneg (a : K) : 0 ≤ valS sg S (C a : MvPolynomial (L × Fin r) K) := by
  classical
  rw [le_valS_iff, subV_C]
  intro β
  rw [coeff_C]
  split_ifs
  · exact lord_C_nonneg _
  · rw [lord_zero]; exact le_top

theorem valS_C_mul_le (a : K) (F : MvPolynomial (L × Fin r) K) :
    valS sg S F ≤ valS sg S (C a * F) := by
  have h := valS_mul_le sg S (C a) F
  refine le_trans ?_ h
  calc valS sg S F = 0 + valS sg S F := (zero_add _).symm
    _ ≤ _ := add_le_add (valS_C_nonneg sg S a) le_rfl

theorem valS_smul_le (a : K) (F : MvPolynomial (L × Fin r) K) :
    valS sg S F ≤ valS sg S (a • F) := by
  rw [smul_eq_C_mul]; exact valS_C_mul_le sg S a F

end Basic

section Exps

variable {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]

theorem eOut_apply (α : L × Fin r →₀ ℕ) (x : L × Fin r) :
    eOut out α x = if out x.1 then α x else 0 := by
  unfold eOut; rw [Finsupp.filter_apply]

theorem eIn_apply (α : L × Fin r →₀ ℕ) (x : L × Fin r) :
    eIn out α x = if out x.1 then 0 else α x := by
  unfold eIn; rw [Finsupp.filter_apply]
  by_cases h : out x.1 <;> simp [h]

theorem eOut_add_eIn (α : L × Fin r →₀ ℕ) : eOut out α + eIn out α = α :=
  Finsupp.filter_add_filter_not α _

theorem eOut_add (α β : L × Fin r →₀ ℕ) : eOut out (α + β) = eOut out α + eOut out β :=
  Finsupp.filter_add

theorem eIn_add (α β : L × Fin r →₀ ℕ) : eIn out (α + β) = eIn out α + eIn out β :=
  Finsupp.filter_add

theorem eOut_eOut (α : L × Fin r →₀ ℕ) : eOut out (eOut out α) = eOut out α := by
  ext x; simp only [eOut_apply]; split_ifs <;> rfl

theorem eIn_eIn (α : L × Fin r →₀ ℕ) : eIn out (eIn out α) = eIn out α := by
  ext x; simp only [eIn_apply]; split_ifs <;> rfl

theorem eIn_eOut (α : L × Fin r →₀ ℕ) : eIn out (eOut out α) = 0 := by
  ext x; simp only [eIn_apply, eOut_apply, Finsupp.coe_zero, Pi.zero_apply]; split_ifs <;> rfl

theorem eOut_eIn (α : L × Fin r →₀ ℕ) : eOut out (eIn out α) = 0 := by
  ext x; simp only [eIn_apply, eOut_apply, Finsupp.coe_zero, Pi.zero_apply]; split_ifs <;> rfl

theorem eOut_zero : eOut out (0 : L × Fin r →₀ ℕ) = 0 := by
  ext x; simp [eOut_apply]

theorem eIn_zero : eIn out (0 : L × Fin r →₀ ℕ) = 0 := by
  ext x; simp [eIn_apply]

theorem eIn_eq_self_of_eOut_eq_zero {α : L × Fin r →₀ ℕ} (h : eOut out α = 0) : eIn out α = α := by
  have := eOut_add_eIn out α
  rwa [h, zero_add] at this

theorem eOut_le (α : L × Fin r →₀ ℕ) : eOut out α ≤ α := by
  intro x; rw [eOut_apply]; split_ifs <;> simp

theorem sub_eOut (α : L × Fin r →₀ ℕ) : α - eOut out α = eIn out α := by
  ext x; simp only [Finsupp.coe_tsub, Pi.sub_apply, eOut_apply, eIn_apply]; split_ifs <;> simp

end Exps

section Subst

variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)

def subX (x : L × Fin r) : MvPolynomial (L × Fin r) R :=
  if x.1 ∈ S then
    (if sg x.1 then ∑ b, MvPolynomial.C (A x.2 b) * X (x.1, b)
     else ∑ b, MvPolynomial.C (B x.2 b) * X (x.1, b))
  else X x

theorem substS_X (x : L × Fin r) : substS ι sg S A B (X x) = subX sg S A B x := by
  simp [substS, subX]

theorem substS_C (c : K) : substS ι sg S A B (C c) = C (ι c) := by
  simp [substS]

theorem substS_monomial (α : L × Fin r →₀ ℕ) (c : K) :
    substS ι sg S A B (monomial α c) = C (ι c) * α.prod fun x k => subX sg S A B x ^ k := by
  unfold substS
  rw [eval₂Hom_monomial]
  rfl

theorem substS_monomial' (α : L × Fin r →₀ ℕ) (c : K) :
    substS ι sg S A B (monomial α c) = C (ι c) * substS ι sg S A B (monomial α 1) := by
  rw [substS_monomial, substS_monomial ι sg S A B α 1, map_one, map_one, one_mul]

theorem substS_eq_sum (F : MvPolynomial (L × Fin r) K) :
    substS ι sg S A B F =
      ∑ α ∈ F.support, C (ι (F.coeff α)) * substS ι sg S A B (monomial α 1) := by
  conv_lhs => rw [F.as_sum, map_sum]
  exact Finset.sum_congr rfl fun α _ => substS_monomial' ι sg S A B α _

theorem coeff_substS (F : MvPolynomial (L × Fin r) K) (β : L × Fin r →₀ ℕ) :
    (substS ι sg S A B F).coeff β =
      ∑ α ∈ F.support, ι (F.coeff α) * (substS ι sg S A B (monomial α 1)).coeff β := by
  rw [substS_eq_sum, coeff_sum]
  exact Finset.sum_congr rfl fun α _ => coeff_C_mul _ _ _

theorem substS_mem (T : Subring (MvPolynomial (L × Fin r) R)) (hC : ∀ c : K, C (ι c) ∈ T)
    (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ x ∈ α.support, subX sg S A B x ∈ T) : substS ι sg S A B F ∈ T := by
  rw [F.as_sum, map_sum]
  refine Subring.sum_mem _ fun α hα => ?_
  rw [substS_monomial]
  refine Subring.mul_mem _ (hC _) ?_
  exact Subring.prod_mem _ fun x hx => Subring.pow_mem _ (h α hα x hx) _

theorem substS_monomial_of_free (α : L × Fin r →₀ ℕ) (c : K) (h : ∀ x ∈ α.support, x.1 ∉ S) :
    substS ι sg S A B (monomial α c) = monomial α (ι c) := by
  rw [substS_monomial]
  have : (α.prod fun x k => subX sg S A B x ^ k) = α.prod fun x k => (X x : MvPolynomial (L × Fin r) R) ^ k := by
    refine Finset.prod_congr rfl fun x hx => ?_
    simp only [subX, if_neg (h x hx)]
  rw [this, monomial_eq]

variable (out : L → Prop) [DecidablePred out]

theorem subX_mem_supported (x : L × Fin r) (hx : ¬ out x.1) :
    subX sg S A B x ∈ supported R {y : L × Fin r | ¬ out y.1} := by
  have hX : ∀ b, (X (x.1, b) : MvPolynomial (L × Fin r) R) ∈ supported R {y : L × Fin r | ¬ out y.1} := by
    intro b
    rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨(x.1, b), hx, rfl⟩
  have hCm : ∀ a : R, (C a : MvPolynomial (L × Fin r) R) ∈ supported R {y : L × Fin r | ¬ out y.1} :=
    fun a => Subalgebra.algebraMap_mem _ a
  unfold subX
  split_ifs
  · exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (hCm _) (hX b)
  · exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (hCm _) (hX b)
  · exact hX x.2

theorem coeff_substS_eIn_eq_zero (α δ : L × Fin r →₀ ℕ) (hδ : eOut out δ ≠ 0) :
    (substS ι sg S A B (monomial (eIn out α) 1)).coeff δ = 0 := by
  have hmem : substS ι sg S A B (monomial (eIn out α) 1) ∈
      (supported R {y : L × Fin r | ¬ out y.1}).toSubring := by
    refine substS_mem ι sg S A B _ (fun c => Subalgebra.algebraMap_mem _ _) _ ?_
    intro γ hγ x hx
    refine subX_mem_supported sg S A B out x ?_
    have hγ' : γ = eIn out α := by
      classical
      have := support_monomial_subset hγ
      simpa using this
    rw [hγ', Finsupp.mem_support_iff, eIn_apply] at hx
    intro ho
    rw [if_pos ho] at hx
    exact hx rfl
  have hv := mem_supported.mp (Subalgebra.mem_toSubring.mp hmem)
  by_contra hne
  apply hδ
  ext x
  rw [eOut_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with ho
  · by_contra hx
    have : x ∈ (substS ι sg S A B (monomial (eIn out α) 1)).vars :=
      (mem_vars_iff_mem_support x).mpr ⟨δ, mem_support_iff.mpr hne, Finsupp.mem_support_iff.mpr hx⟩
    exact hv (Finset.mem_coe.mpr this) ho
  · rfl

theorem substS_monomial_split (hout : ∀ i ∈ S, ¬ out i) (α : L × Fin r →₀ ℕ) :
    substS ι sg S A B (monomial α 1) =
      monomial (eOut out α) 1 * substS ι sg S A B (monomial (eIn out α) 1) := by
  have h1 : (monomial α (1 : K)) = monomial (eOut out α) 1 * monomial (eIn out α) 1 := by
    rw [monomial_mul, eOut_add_eIn, one_mul]
  conv_lhs => rw [h1, map_mul]
  rw [substS_monomial_of_free ι sg S A B (eOut out α) 1, map_one]
  intro x hx hxS
  rw [Finsupp.mem_support_iff, eOut_apply, if_neg (hout _ hxS)] at hx
  exact hx rfl

theorem coeff_substS_monomial (hout : ∀ i ∈ S, ¬ out i) (α γ : L × Fin r →₀ ℕ) :
    (substS ι sg S A B (monomial α 1)).coeff γ =
      if eOut out γ = eOut out α then (substS ι sg S A B (monomial (eIn out α) 1)).coeff (eIn out γ)
      else 0 := by
  rw [substS_monomial_split ι sg S A B out hout α, coeff_monomial_mul', one_mul]
  split_ifs with h1 h2 h2
  · rw [← h2, sub_eOut]
  · apply coeff_substS_eIn_eq_zero
    intro h0
    apply h2
    ext x
    have hx := DFunLike.congr_fun h0 x
    have hle := h1 x
    simp only [eOut_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply] at hx hle ⊢
    split_ifs with ho
    · simp only [if_pos ho] at hx hle
      omega
    · rfl
  · exact absurd (h2 ▸ eOut_le out γ) h1
  · rfl

end Subst

section CoefOut

variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]

theorem coefOut_zero (μ : L × Fin r →₀ ℕ) :
    coefOut out μ (0 : MvPolynomial (L × Fin r) K) = 0 := by
  simp [coefOut]

theorem coefOut_eq_sum (μ : L × Fin r →₀ ℕ) (F : MvPolynomial (L × Fin r) K)
    (s : Finset (L × Fin r →₀ ℕ)) (hs : F.support ⊆ s) :
    coefOut out μ F = ∑ α ∈ s, if eOut out α = μ then monomial (eIn out α) (F.coeff α) else 0 := by
  unfold coefOut
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [notMem_support_iff.mp hα, monomial_zero, ite_self]

theorem coefOut_add (μ : L × Fin r →₀ ℕ) (F G : MvPolynomial (L × Fin r) K) :
    coefOut out μ (F + G) = coefOut out μ F + coefOut out μ G := by
  rw [coefOut_eq_sum out μ (F + G) (F.support ∪ G.support) support_add,
    coefOut_eq_sum out μ F (F.support ∪ G.support) Finset.subset_union_left,
    coefOut_eq_sum out μ G (F.support ∪ G.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [coeff_add, map_add]
  · rw [add_zero]

theorem coefOut_smul (μ : L × Fin r →₀ ℕ) (a : K) (F : MvPolynomial (L × Fin r) K) :
    coefOut out μ (a • F) = a • coefOut out μ F := by
  rw [coefOut_eq_sum out μ (a • F) F.support support_smul, coefOut, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [coeff_smul, smul_monomial]
  · rw [smul_zero]

def coefOutL (μ : L × Fin r →₀ ℕ) : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K where
  toFun := coefOut out μ
  map_add' := coefOut_add out μ
  map_smul' := coefOut_smul out μ

theorem coefOutL_apply (μ : L × Fin r →₀ ℕ) (F : MvPolynomial (L × Fin r) K) :
    coefOutL out μ F = coefOut out μ F := rfl

theorem coefOut_sum {ι : Type} (μ : L × Fin r →₀ ℕ) (s : Finset ι)
    (f : ι → MvPolynomial (L × Fin r) K) :
    coefOut out μ (∑ i ∈ s, f i) = ∑ i ∈ s, coefOut out μ (f i) :=
  map_sum (coefOutL out μ) f s

theorem coefOut_monomial (μ α : L × Fin r →₀ ℕ) (c : K) :
    coefOut out μ (monomial α c) = if eOut out α = μ then monomial (eIn out α) c else 0 := by
  rw [coefOut_eq_sum out μ (monomial α c) {α} support_monomial_subset, Finset.sum_singleton,
    coeff_monomial, if_pos rfl]

theorem coeff_coefOut (μ β : L × Fin r →₀ ℕ) (F : MvPolynomial (L × Fin r) K) :
    (coefOut out μ F).coeff β =
      if eOut out β = 0 ∧ eOut out μ = μ then F.coeff (μ + β) else 0 := by
  induction F using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [coefOut_monomial]
    by_cases h1 : eOut out α = μ
    · rw [if_pos h1, coeff_monomial, coeff_monomial]
      have hμ : eOut out μ = μ := by rw [← h1, eOut_eOut]
      by_cases h2 : eIn out α = β
      · have h3 : eOut out β = 0 := by rw [← h2, eOut_eIn]
        have h4 : α = μ + β := by rw [← h1, ← h2, eOut_add_eIn]
        rw [if_pos h2, if_pos ⟨h3, hμ⟩, if_pos h4]
      · rw [if_neg h2]
        split_ifs with h3 h4
        · exfalso; apply h2
          rw [h4, eIn_add, ← hμ, eIn_eOut, zero_add, eIn_eq_self_of_eOut_eq_zero out h3.1]
        · rfl
        · rfl
    · rw [if_neg h1, coeff_zero, coeff_monomial]
      split_ifs with h3 h4
      · exfalso; apply h1
        rw [h4, eOut_add, h3.1, h3.2, add_zero]
      · rfl
      · rfl
  | add p q hp hq =>
    rw [coefOut_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp

theorem eOut_eq_zero_of_mem_support_coefOut {μ β : L × Fin r →₀ ℕ} {F : MvPolynomial (L × Fin r) K}
    (h : β ∈ (coefOut out μ F).support) : eOut out β = 0 := by
  rw [mem_support_iff, coeff_coefOut] at h
  by_contra h0
  exact h (if_neg fun hh => h0 hh.1)

theorem add_mem_support_of_mem_support_coefOut {μ β : L × Fin r →₀ ℕ}
    {F : MvPolynomial (L × Fin r) K} (h : β ∈ (coefOut out μ F).support) : μ + β ∈ F.support := by
  rw [mem_support_iff, coeff_coefOut] at h
  rw [mem_support_iff]
  intro h0
  apply h
  split_ifs
  · exact h0
  · rfl

theorem sum_mul_coefOut (g : (L × Fin r →₀ ℕ) → MvPolynomial (L × Fin r) K)
    (F : MvPolynomial (L × Fin r) K) :
    ∑ μ ∈ F.support.image (eOut out), g μ * coefOut out μ F =
      ∑ α ∈ F.support, g (eOut out α) * monomial (eIn out α) (F.coeff α) := by
  unfold coefOut
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α hα => ?_
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ hα)]

theorem sum_coefOut (F : MvPolynomial (L × Fin r) K) :
    F = ∑ μ ∈ F.support.image (eOut out), monomial μ 1 * coefOut out μ F := by
  rw [sum_mul_coefOut out (fun μ => monomial μ 1) F]
  conv_lhs => rw [F.as_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [monomial_mul, eOut_add_eIn, one_mul]

variable (sg : L → Bool) (S : Finset L)

theorem valS_coefOut_le (hout : ∀ i ∈ S, ¬ out i) (μ : L × Fin r →₀ ℕ)
    (F : MvPolynomial (L × Fin r) K) : valS sg S F ≤ valS sg S (coefOut out μ F) := by
  rw [le_valS_iff]
  intro β
  by_cases hμ : ∃ α ∈ F.support, eOut out α = μ
  · obtain ⟨α₀, -, hα₀⟩ := hμ
    have hμ1 : eOut out μ = μ := by rw [← hα₀, eOut_eOut]
    have hμ2 : eIn out μ = 0 := by rw [← hα₀, eIn_eOut]
    have hexp : (subV sg S (coefOut out μ F)).coeff β =
        ∑ α ∈ F.support, if eOut out α = μ then
          lauι K r (F.coeff α) * (subV sg S (monomial (eIn out α) 1)).coeff β else 0 := by
      unfold coefOut
      rw [map_sum, coeff_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      split_ifs
      · rw [substS_monomial', coeff_C_mul]
      · rw [map_zero, coeff_zero]
    by_cases hβ : eOut out β = 0
    · have hβ2 : eIn out β = β := eIn_eq_self_of_eOut_eq_zero out hβ
      have : (subV sg S (coefOut out μ F)).coeff β = (subV sg S F).coeff (μ + β) := by
        rw [hexp, coeff_substS]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [coeff_substS_monomial _ sg S _ _ out hout α (μ + β), eOut_add, eIn_add, hμ1, hμ2, hβ, hβ2,
          add_zero, zero_add]
        by_cases h : eOut out α = μ
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]
      rw [this]
      exact pge_valS sg S F _
    · rw [hexp]
      refine le_lord_sum _ _ fun α _ => ?_
      split_ifs
      · rw [coeff_substS_eIn_eq_zero _ sg S _ _ out α β hβ, mul_zero, lord_zero]; exact le_top
      · rw [lord_zero]; exact le_top
  · have : coefOut out μ F = 0 := by
      unfold coefOut
      refine Finset.sum_eq_zero fun α hα => ?_
      rw [if_neg fun h => hμ ⟨α, hα, h⟩]
    rw [this, map_zero, coeff_zero, lord_zero]; exact le_top

theorem valS_outside_linear (Φ : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (hout : ∀ i ∈ S, ¬ out i)
    (h1 : ∀ α, Φ (monomial α 1) = monomial (eIn out α) 1 * Φ (monomial (eOut out α) 1))
    (h2 : ∀ α, 0 ≤ valS sg S (Φ (monomial (eOut out α) 1))) (F : MvPolynomial (L × Fin r) K) :
    valS sg S F ≤ valS sg S (Φ F) := by
  have hΦ : Φ F = ∑ μ ∈ F.support.image (eOut out), Φ (monomial μ 1) * coefOut out μ F := by
    rw [sum_mul_coefOut out (fun μ => Φ (monomial μ 1)) F]
    conv_lhs => rw [F.as_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have : monomial α (F.coeff α) = F.coeff α • (monomial α (1 : K)) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, h1 α, smul_eq_C_mul]
    have h3 : monomial (eIn out α) (F.coeff α) = C (F.coeff α) * monomial (eIn out α) (1 : K) := by
      rw [C_mul_monomial, mul_one]
    rw [h3]; ring
  rw [hΦ]
  refine valS_sum_le sg S _ _ _ fun μ hμ => ?_
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hμ
  refine le_trans ?_ (valS_mul_le sg S _ _)
  calc valS sg S F = 0 + valS sg S F := (zero_add _).symm
    _ ≤ _ := add_le_add (h2 α) (valS_coefOut_le out sg S hout _ F)

end CoefOut

section Nonneg

variable {K : Type} [Field K]

theorem lord_nonneg_of_mem {R : Type} [CommRing R] (f : LaurentPolynomial R)
    (hf : f ∈ (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R).range) : 0 ≤ lord f := by
  obtain ⟨q, rfl⟩ := hf
  unfold lord
  apply Finset.le_min
  intro n hn
  rw [LaurentPolynomial.support_coeff_toLaurent] at hn
  simp only [Finset.mem_map, Nat.castEmbedding_apply] at hn
  obtain ⟨m, -, rfl⟩ := hn
  exact_mod_cast Nat.zero_le m

theorem hMat_mem (r : ℕ) (a b : Fin r) :
    hMat K r a b ∈ (Polynomial.toLaurent : Polynomial (GenF K r) →+* LauF K r).range := by
  unfold hMat sDiag Formalism.MainNotions.G.gL Formalism.MainNotions.G.gLinv
  rw [Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Matrix.map_apply]
  refine Subring.sum_mem _ fun k _ => ?_
  refine Subring.mul_mem _ ?_ (RingHom.mem_range.mpr ⟨Polynomial.C _, Polynomial.toLaurent_C _⟩)
  refine Subring.sum_mem _ fun l _ => Subring.mul_mem _
    (RingHom.mem_range.mpr ⟨Polynomial.C _, Polynomial.toLaurent_C _⟩) ?_
  simp only [Matrix.diagonal_apply]
  split_ifs <;> first
    | exact RingHom.mem_range.mpr ⟨Polynomial.X, Polynomial.toLaurent_X⟩
    | exact Subring.one_mem _
    | exact Subring.zero_mem _

variable {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)

theorem valS_nonneg_of_vecS (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ i a, α (i, a) ≠ 0 → i ∈ S → sg i = true) : 0 ≤ valS sg S F := by
  have key : subV sg S F ∈
      (MvPolynomial.map (σ := L × Fin r)
        (Polynomial.toLaurent : Polynomial (GenF K r) →+* LauF K r)).range := by
    refine substS_mem _ sg S _ _ _ ?_ F ?_
    · intro c
      refine ⟨MvPolynomial.C (Polynomial.C ((algebraMap (MvPolynomial (Fin r × Fin r) K) (GenF K r))
        (MvPolynomial.C c))), ?_⟩
      simp [lauι, Formalism.MainNotions.G.coefL]
    · intro α hα x hx
      unfold subX
      split_ifs with h1 h2
      · refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ ⟨X (x.1, b), by simp⟩
        obtain ⟨q, hq⟩ := hMat_mem (K := K) r x.2 b
        exact ⟨MvPolynomial.C q, by simp [hq]⟩
      · exact absurd (h α hα x.1 x.2 (Finsupp.mem_support_iff.mp hx) h1) h2
      · exact ⟨X x, by simp⟩
  rw [le_valS_iff]
  intro β
  apply lord_nonneg_of_mem
  obtain ⟨q, hq⟩ := key
  rw [← hq, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩

theorem valS_nonneg_of_free (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ i ∈ S, ∀ a, α (i, a) = 0) : 0 ≤ valS sg S F :=
  valS_nonneg_of_vecS sg S F fun α hα i a hne hi => absurd (h α hα i hi a) hne

theorem valS_nonneg_of_vec (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ i a, α (i, a) ≠ 0 → sg i = true) : 0 ≤ valS sg S F :=
  valS_nonneg_of_vecS sg S F fun α hα i a hne _ => h α hα i a hne

end Nonneg

section Rename

variable {K : Type} [Field K] {L : Type} [DecidableEq L] {L' : Type} [DecidableEq L'] {r : ℕ}

theorem substS_rename {R : Type} [CommRing R] (ι : K →+* R) (A B : Matrix (Fin r) (Fin r) R)
    (f : L → L') (hf : Function.Injective f) (sg' : L' → Bool) (S' : Finset L')
    (F : MvPolynomial (L × Fin r) K) :
    substS ι sg' S' A B (rename (Prod.map f id) F) =
      rename (Prod.map f id) (substS ι (sg' ∘ f) (S'.preimage f hf.injOn) A B F) := by
  have : (substS ι sg' S' A B).comp (rename (Prod.map f (id : Fin r → Fin r))).toRingHom =
      ((rename (Prod.map f (id : Fin r → Fin r)) :
        MvPolynomial (L × Fin r) R →ₐ[R] MvPolynomial (L' × Fin r) R).toRingHom).comp
        (substS ι (sg' ∘ f) (S'.preimage f hf.injOn) A B) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [substS_C]
    · intro x
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, substS_X]
      unfold subX
      simp only [Prod.map_fst, Prod.map_snd, id_eq, Finset.mem_preimage, Function.comp_apply]
      split_ifs <;> simp [map_sum, rename_X]
  exact RingHom.congr_fun this F

theorem valS_rename (f : L → L') (hf : Function.Injective f) (sg' : L' → Bool) (S' : Finset L')
    (F : MvPolynomial (L × Fin r) K) :
    valS sg' S' (rename (Prod.map f id) F) = valS (sg' ∘ f) (S'.preimage f hf.injOn) F := by
  have hinj : Function.Injective (Prod.map f (id : Fin r → Fin r)) :=
    hf.prodMap Function.injective_id
  have key : ∀ n : WithTop ℤ, n ≤ valS sg' S' (rename (Prod.map f id) F) ↔
      n ≤ valS (sg' ∘ f) (S'.preimage f hf.injOn) F := by
    intro n
    rw [le_valS_iff, le_valS_iff, subV, substS_rename _ _ _ f hf]
    constructor
    · intro h β
      have := h (Finsupp.mapDomain (Prod.map f id) β)
      rwa [coeff_rename_mapDomain _ hinj] at this
    · intro h β'
      by_cases hβ : ∃ β, Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β = β'
      · obtain ⟨β, rfl⟩ := hβ
        rw [coeff_rename_mapDomain _ hinj]
        exact h β
      · rw [coeff_rename_eq_zero, lord_zero]
        · exact le_top
        · intro u hu
          exact absurd ⟨u, hu⟩ hβ
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

end Rename

section Hcomp

variable {L : Type} {r : ℕ}

theorem ldeg_add (α β : L × Fin r →₀ ℕ) (i : L) : ldeg (α + β) i = ldeg α i + ldeg β i := by
  unfold ldeg
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]

theorem ldeg_zero (i : L) : ldeg (0 : L × Fin r →₀ ℕ) i = 0 := by
  simp [ldeg]

theorem ldeg_single [DecidableEq L] (i : L) (b : Fin r) (k : ℕ) (j : L) :
    ldeg (Finsupp.single (i, b) k) j = if j = i then k else 0 := by
  classical
  unfold ldeg
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ hab
      rw [Finsupp.single_apply, if_neg]
      intro hh; exact hab (Prod.mk.inj hh).2.symm
    · intro hb; exact absurd (Finset.mem_univ b) hb
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro hh; exact h (Prod.mk.inj hh).1.symm

def HomD {R : Type} [CommSemiring R] (d : L → ℕ) (G : MvPolynomial (L × Fin r) R) : Prop :=
  ∀ β ∈ G.support, ∀ i, ldeg β i = d i

section HomD

variable {R : Type} [CommSemiring R]

theorem HomD_congr {d d' : L → ℕ} (h : ∀ i, d i = d' i) {G : MvPolynomial (L × Fin r) R}
    (hG : HomD d G) : HomD d' G := fun β hβ i => (hG β hβ i).trans (h i)

theorem HomD_one : HomD (fun _ => 0) (1 : MvPolynomial (L × Fin r) R) := by
  classical
  intro β hβ i
  have : β = 0 := by
    have := support_monomial_subset (R := R) (s := (0 : L × Fin r →₀ ℕ)) (a := 1) hβ
    simpa using this
  rw [this, ldeg_zero]

theorem HomD_mul {d d' : L → ℕ} {G G' : MvPolynomial (L × Fin r) R} (hG : HomD d G)
    (hG' : HomD d' G') : HomD (fun i => d i + d' i) (G * G') := by
  classical
  intro β hβ i
  obtain ⟨b1, h1, b2, h2, rfl⟩ := Finset.mem_add.mp (support_mul G G' hβ)
  rw [ldeg_add, hG b1 h1 i, hG' b2 h2 i]

theorem HomD_sum {ι : Type} {d : L → ℕ} (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) R)
    (h : ∀ k ∈ s, HomD d (f k)) : HomD d (∑ k ∈ s, f k) := by
  classical
  intro β hβ i
  obtain ⟨k, hk, hkβ⟩ := Finset.mem_biUnion.mp (support_sum hβ)
  exact h k hk β hkβ i

theorem HomD_C_mul_X [DecidableEq L] (c : R) (i : L) (b b' : Fin r) :
    HomD (ldeg (Finsupp.single (i, b') 1)) (C c * X (i, b) : MvPolynomial (L × Fin r) R) := by
  intro β hβ j
  have hm : (C c * X (i, b) : MvPolynomial (L × Fin r) R) = monomial (Finsupp.single (i, b) 1) c := by
    rw [X, C_mul_monomial, mul_one]
  rw [hm] at hβ
  have : β = Finsupp.single (i, b) 1 := by
    have := support_monomial_subset hβ
    simpa using this
  rw [this, ldeg_single, ldeg_single]

end HomD

variable {K : Type} [Field K] [DecidableEq L] {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)

theorem HomD_subX (x : L × Fin r) : HomD (ldeg (Finsupp.single x 1)) (subX sg S A B x) := by
  unfold subX
  split_ifs
  · exact HomD_sum _ _ fun b _ => HomD_C_mul_X _ x.1 b x.2
  · exact HomD_sum _ _ fun b _ => HomD_C_mul_X _ x.1 b x.2
  · have := HomD_C_mul_X (R := R) 1 x.1 x.2 x.2
    rwa [map_one, one_mul] at this

theorem HomD_substS_monomial (α : L × Fin r →₀ ℕ) :
    HomD (ldeg α) (substS ι sg S A B (monomial α 1)) := by
  induction α using Finsupp.induction_linear with
  | zero =>
    have : (monomial (0 : L × Fin r →₀ ℕ) (1 : K)) = 1 := rfl
    rw [this, map_one]
    exact HomD_congr (fun i => (ldeg_zero i).symm) HomD_one
  | add α β hα hβ =>
    have : (monomial (α + β) (1 : K)) = monomial α 1 * monomial β 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul]
    exact HomD_congr (fun i => (ldeg_add α β i).symm) (HomD_mul hα hβ)
  | single x k =>
    rw [← X_pow_eq_monomial, map_pow, substS_X]
    induction k with
    | zero =>
      rw [pow_zero, Finsupp.single_zero]
      exact HomD_congr (fun i => (ldeg_zero i).symm) HomD_one
    | succ k ih =>
      rw [pow_succ, Finsupp.single_add]
      exact HomD_congr (fun i => (ldeg_add _ _ i).symm) (HomD_mul ih (HomD_subX sg S A B x))

theorem coeff_substS_monomial_eq_zero (α β : L × Fin r →₀ ℕ) (h : ¬ ∀ i, ldeg β i = ldeg α i) :
    (substS ι sg S A B (monomial α 1)).coeff β = 0 := by
  by_contra hne
  exact h (HomD_substS_monomial ι sg S A B α β (mem_support_iff.mpr hne))

variable [Fintype L]

def hcomp (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) : MvPolynomial (L × Fin r) K :=
  ∑ α ∈ F.support, if (∀ i, ldeg α i = d i) then monomial α (F.coeff α) else 0

theorem coeff_hcomp (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) (β : L × Fin r →₀ ℕ) :
    (hcomp d F).coeff β = if (∀ i, ldeg β i = d i) then F.coeff β else 0 := by
  unfold hcomp
  rw [coeff_sum]
  by_cases hβ : β ∈ F.support
  · rw [Finset.sum_eq_single β]
    · split_ifs
      · rw [coeff_monomial, if_pos rfl]
      · rw [coeff_zero]
    · intro α _ hne
      split_ifs
      · rw [coeff_monomial, if_neg hne]
      · rw [coeff_zero]
    · intro h; exact absurd hβ h
  · rw [notMem_support_iff.mp hβ, ite_self]
    refine Finset.sum_eq_zero fun α hα => ?_
    split_ifs
    · rw [coeff_monomial, if_neg]
      intro h; exact hβ (h ▸ hα)
    · rw [coeff_zero]

theorem hcomp_eq_dg (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    hcomp d F = dg (fun α => if (∀ i, ldeg α i = d i) then (1 : K) else 0) F := by
  ext β
  rw [coeff_hcomp, coeff_dg]
  split_ifs <;> simp

theorem hcomp_add (d : L → ℕ) (F G : MvPolynomial (L × Fin r) K) :
    hcomp d (F + G) = hcomp d F + hcomp d G := by
  simp only [hcomp_eq_dg, map_add]

theorem hcomp_smul (d : L → ℕ) (a : K) (F : MvPolynomial (L × Fin r) K) :
    hcomp d (a • F) = a • hcomp d F := by
  simp only [hcomp_eq_dg, map_smul]

theorem hcomp_sum {κ : Type} (d : L → ℕ) (s : Finset κ) (f : κ → MvPolynomial (L × Fin r) K) :
    hcomp d (∑ k ∈ s, f k) = ∑ k ∈ s, hcomp d (f k) := by
  simp only [hcomp_eq_dg, map_sum]

theorem hcomp_mem_PolK (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) : hcomp d F ∈ PolK K r d := by
  rw [mem_PolK_iff]
  intro α hα
  rw [mem_support_iff, coeff_hcomp] at hα
  by_contra h
  exact hα (if_neg h)

theorem hcomp_of_mem (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) (hF : F ∈ PolK K r d) :
    hcomp d F = F := by
  ext β
  rw [coeff_hcomp]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h ((mem_PolK_iff d F).mp hF β (mem_support_iff.mpr (Ne.symm hne)))

theorem support_hcomp_subset (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    (hcomp d F).support ⊆ F.support := by
  intro β hβ
  rw [mem_support_iff, coeff_hcomp] at hβ
  rw [mem_support_iff]
  intro h0
  apply hβ
  rw [h0, ite_self]

theorem sum_hcomp (F : MvPolynomial (L × Fin r) K) :
    F = ∑ d ∈ F.support.image (fun α i => ldeg α i), hcomp d F := by
  ext β
  rw [coeff_sum]
  simp only [coeff_hcomp]
  by_cases hβ : β ∈ F.support
  · rw [Finset.sum_eq_single (fun i => ldeg β i)]
    · rw [if_pos fun i => rfl]
    · intro d _ hd
      rw [if_neg]
      intro h; exact hd (funext fun i => (h i).symm)
    · intro h; exact absurd (Finset.mem_image_of_mem _ hβ) h
  · rw [notMem_support_iff.mp hβ]
    simp

theorem coeff_subV_hcomp (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) (β : L × Fin r →₀ ℕ) :
    (substS ι sg S A B (hcomp d F)).coeff β =
      if (∀ i, ldeg β i = d i) then (substS ι sg S A B F).coeff β else 0 := by
  have hexp : (substS ι sg S A B (hcomp d F)).coeff β =
      ∑ α ∈ F.support, if (∀ i, ldeg α i = d i) then
        ι (F.coeff α) * (substS ι sg S A B (monomial α 1)).coeff β else 0 := by
    unfold hcomp
    rw [map_sum, coeff_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs
    · rw [substS_monomial', coeff_C_mul]
    · rw [map_zero, coeff_zero]
  rw [hexp]
  split_ifs with hβ
  · rw [coeff_substS]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs with hα
    · rfl
    · rw [coeff_substS_monomial_eq_zero, mul_zero]
      intro h; exact hα fun i => (h i).symm.trans (hβ i)
  · refine Finset.sum_eq_zero fun α _ => ?_
    split_ifs with hα
    · rw [coeff_substS_monomial_eq_zero, mul_zero]
      intro h; exact hβ fun i => (h i).trans (hα i)
    · rfl

theorem valS_hcomp_le (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    valS sg S F ≤ valS sg S (hcomp d F) := by
  rw [le_valS_iff]
  intro β
  rw [subV, coeff_subV_hcomp]
  split_ifs
  · exact pge_valS sg S F β
  · rw [lord_zero]; exact le_top

end Hcomp

section Vala

theorem toR_top : toR ⊤ = ⊤ := rfl

theorem toR_coe (n : ℤ) : toR (n : WithTop ℤ) = (((n : ℤ) : ℝ) : WithTop ℝ) := rfl

theorem le_toR_iff (θ : ℝ) (x : WithTop ℤ) :
    ((θ : ℝ) : WithTop ℝ) ≤ toR x ↔ ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => simp [toR_top]
  | coe n => rw [toR_coe, WithTop.coe_le_coe, WithTop.coe_le_coe, Int.ceil_le]

theorem toR_mono {x y : WithTop ℤ} (h : x ≤ y) : toR x ≤ toR y := by
  induction y using WithTop.recTopCoe with
  | top => simp [toR_top]
  | coe n =>
    induction x using WithTop.recTopCoe with
    | top => exact absurd h (by simp)
    | coe m =>
      rw [toR_coe, toR_coe, WithTop.coe_le_coe]
      exact_mod_cast WithTop.coe_le_coe.mp h

theorem toR_add (x y : WithTop ℤ) : toR (x + y) = toR x + toR y := by
  induction x using WithTop.recTopCoe with
  | top => simp [toR_top]
  | coe m =>
    induction y using WithTop.recTopCoe with
    | top => simp [toR_top]
    | coe n =>
      rw [← WithTop.coe_add, toR_coe, toR_coe, toR_coe, ← WithTop.coe_add]
      push_cast; rfl

variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)

theorem vala_iff (θ : ℝ) (F : MvPolynomial (L × Fin r) K) :
    vala sg S θ F ↔ ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤ valS sg S F := le_toR_iff θ _

theorem vala_iff_Aset (θ : ℝ) (F : MvPolynomial (L × Fin r) K) :
    vala sg S θ F ↔ F ∈ Aset sg S ⌈θ⌉ := vala_iff sg S θ F

theorem vala_int_iff (n : ℤ) (F : MvPolynomial (L × Fin r) K) :
    vala sg S (n : ℝ) F ↔ F ∈ Aset sg S n := by
  rw [vala_iff_Aset, Int.ceil_intCast]

variable {sg S}

theorem vala_mono {θ θ' : ℝ} (h : θ' ≤ θ) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ' F := le_trans (WithTop.coe_le_coe.mpr h) hF

theorem vala_of_le {θ : ℝ} {L' : Type} [DecidableEq L'] {sg' : L' → Bool} {S' : Finset L'}
    {F : MvPolynomial (L × Fin r) K} {G : MvPolynomial (L' × Fin r) K}
    (h : valS sg S F ≤ valS sg' S' G) (hF : vala sg S θ F) : vala sg' S' θ G :=
  le_trans hF (toR_mono h)

theorem vala_zero (θ : ℝ) : vala sg S θ (0 : MvPolynomial (L × Fin r) K) := by
  unfold vala; rw [valS_zero, toR_top]; exact le_top

theorem vala_add {θ : ℝ} {F G : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F)
    (hG : vala sg S θ G) : vala sg S θ (F + G) := by
  rw [vala_iff] at *
  exact le_trans (le_min hF hG) (valS_add_le sg S F G)

theorem vala_sum {θ : ℝ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) K)
    (h : ∀ i ∈ s, vala sg S θ (f i)) : vala sg S θ (∑ i ∈ s, f i) := by
  rw [vala_iff]
  exact valS_sum_le sg S s f _ fun i hi => (vala_iff sg S θ _).mp (h i hi)

theorem vala_smul {θ : ℝ} (a : K) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (a • F) := vala_of_le (valS_smul_le sg S a F) hF

theorem vala_C_mul {θ : ℝ} (a : K) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (C a * F) := vala_of_le (valS_C_mul_le sg S a F) hF

theorem vala_neg {θ : ℝ} {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (-F) := by
  have := vala_smul (-1 : K) hF
  rwa [neg_smul, one_smul] at this

theorem vala_sub {θ : ℝ} {F G : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F)
    (hG : vala sg S θ G) : vala sg S θ (F - G) := by
  rw [sub_eq_add_neg]; exact vala_add hF (vala_neg hG)

theorem vala_mul {θ₁ θ₂ : ℝ} {F G : MvPolynomial (L × Fin r) K} (hF : vala sg S θ₁ F)
    (hG : vala sg S θ₂ G) : vala sg S (θ₁ + θ₂) (F * G) := by
  unfold vala at *
  refine le_trans ?_ (toR_mono (valS_mul_le sg S F G))
  rw [toR_add, WithTop.coe_add]
  exact add_le_add hF hG

theorem vala_of_nonneg {F : MvPolynomial (L × Fin r) K} (h : 0 ≤ valS sg S F) : vala sg S 0 F := by
  rw [vala_iff, Int.ceil_zero]; exact h

theorem vala_one : vala sg S 0 (1 : MvPolynomial (L × Fin r) K) := by
  have := valS_C_nonneg sg S (1 : K) (r := r)
  rw [map_one] at this
  exact vala_of_nonneg this

theorem vala_pow {θ : ℝ} {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) (k : ℕ) :
    vala sg S (k * θ) (F ^ k) := by
  induction k with
  | zero => simpa using vala_one
  | succ k ih =>
    rw [pow_succ]
    have := vala_mul ih hF
    convert this using 1
    push_cast; ring

theorem vala_mul_left_nonneg {θ : ℝ} {F G : MvPolynomial (L × Fin r) K} (hF : 0 ≤ valS sg S F)
    (hG : vala sg S θ G) : vala sg S θ (F * G) := by
  have := vala_mul (vala_of_nonneg hF) hG
  rwa [zero_add] at this

theorem vala_prod {ι : Type} (s : Finset ι) (θ : ι → ℝ) (f : ι → MvPolynomial (L × Fin r) K)
    (h : ∀ i ∈ s, vala sg S (θ i) (f i)) : vala sg S (∑ i ∈ s, θ i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vala_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact vala_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem vala_coefOut {θ : ℝ} (out : L → Prop) [DecidablePred out] (hout : ∀ i ∈ S, ¬ out i)
    (μ : L × Fin r →₀ ℕ) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (coefOut out μ F) := vala_of_le (valS_coefOut_le out sg S hout μ F) hF

theorem vala_hcomp [Fintype L] {θ : ℝ} (d : L → ℕ) {F : MvPolynomial (L × Fin r) K}
    (hF : vala sg S θ F) : vala sg S θ (hcomp d F) := vala_of_le (valS_hcomp_le sg S d F) hF

theorem vala_outside_linear {θ : ℝ}
    (Φ : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (out : L → Prop) [DecidablePred out] (hout : ∀ i ∈ S, ¬ out i)
    (h1 : ∀ α, Φ (monomial α 1) = monomial (eIn out α) 1 * Φ (monomial (eOut out α) 1))
    (h2 : ∀ α, 0 ≤ valS sg S (Φ (monomial (eOut out α) 1))) {F : MvPolynomial (L × Fin r) K}
    (hF : vala sg S θ F) : vala sg S θ (Φ F) :=
  vala_of_le (valS_outside_linear out sg S Φ hout h1 h2 F) hF

theorem vala_rename_iff {L' : Type} [DecidableEq L'] (f : L → L') (hf : Function.Injective f)
    (sg' : L' → Bool) (S' : Finset L') (θ : ℝ) (F : MvPolynomial (L × Fin r) K) :
    vala sg' S' θ (rename (Prod.map f id) F) ↔ vala (sg' ∘ f) (S'.preimage f hf.injOn) θ F := by
  unfold vala; rw [valS_rename f hf]

theorem vala_of_add_le {θ : ℝ} (k : ℤ) {F G : MvPolynomial (L × Fin r) K}
    (h : valS sg S F + ((k : ℤ) : WithTop ℤ) ≤ valS sg S G) (hF : vala sg S θ F) :
    vala sg S (θ + k) G := by
  unfold vala at *
  refine le_trans ?_ (toR_mono h)
  rw [toR_add, toR_coe, WithTop.coe_add]
  exact add_le_add hF le_rfl

end Vala

section FromV2

variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}

theorem vala_superset_vec (hV2 : V2 K) {θ : ℝ} {S' : Finset L} (hsub : S ⊆ S')
    (hvec : ∀ i ∈ S', i ∉ S → sg i = true) {F : MvPolynomial (L × Fin r) K}
    (hF : vala sg S θ F) : vala sg S' θ F :=
  vala_of_le ((hV2 L sg r S).2.2.1 S' hsub hvec F) hF

theorem vala_X (hV2 : V2 K) (i : L) (a : Fin r) :
    vala sg S (if sg i then 0 else -1) (X (i, a) : MvPolynomial (L × Fin r) K) := by
  have h := (hV2 L sg r S).1 i a
  by_cases hs : sg i = true
  · rw [if_pos hs] at h ⊢
    rw [vala_iff, Int.ceil_zero]; exact h
  · rw [if_neg hs] at h ⊢
    have h1 : ⌈(-1 : ℝ)⌉ = -1 := by
      have := Int.ceil_intCast (R := ℝ) (-1)
      simpa using this
    rw [vala_iff, h1]; exact h

theorem vala_ddiv_letter' (hV2 : V2 K) {θ : ℝ} (i : L) (β : Fin r →₀ ℕ)
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S (θ - (if sg i then (absE β : ℝ) else 0)) (ddiv (onLetter i β) F) := by
  have h := (hV2 L sg r S).2.1 i β F
  have := vala_of_add_le _ h hF
  convert this using 1
  split_ifs <;> simp [sub_eq_add_neg]

theorem vala_ddiv_letter (hV2 : V2 K) {θ : ℝ} (i : L) (β : Fin r →₀ ℕ)
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S (θ - absE β) (ddiv (onLetter i β) F) := by
  refine vala_mono ?_ (vala_ddiv_letter' hV2 i β hF)
  split_ifs
  · exact le_rfl
  · have : (0 : ℝ) ≤ absE β := Nat.cast_nonneg _
    linarith

omit [CharZero K] [Fintype L] [NeZero r] in
theorem dg_eq_sum {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg f F = ∑ α ∈ F.support, monomial α (f α * F.coeff α) := by
  conv_lhs => rw [F.as_sum, map_sum]
  exact Finset.sum_congr rfl fun α _ => dg_monomial f α _

omit [CharZero K] [Fintype L] [NeZero r] in
theorem prod_choose_single {σ : Type} (α : σ →₀ ℕ) (x : σ) (k : ℕ) (hk : k ≤ α x) :
    (α.prod fun y n => ((n.choose (Finsupp.single x k y) : ℕ) : K)) = ((α x).choose k : ℕ) := by
  classical
  unfold Finsupp.prod
  rw [Finset.prod_eq_single x]
  · dsimp only
    rw [Finsupp.single_eq_same]
  · intro y _ hy
    dsimp only
    rw [Finsupp.single_apply, if_neg (Ne.symm hy), Nat.choose_zero_right, Nat.cast_one]
  · intro hx
    have h0 : α x = 0 := Finsupp.notMem_support_iff.mp hx
    have hk0 : k = 0 := by omega
    dsimp only
    rw [Finsupp.single_eq_same, h0, hk0, Nat.choose_zero_right, Nat.cast_one]

omit [CharZero K] [Fintype L] [NeZero r] in
theorem dg_choose_eq {σ : Type} (x : σ) (k : ℕ) (F : MvPolynomial σ K) :
    dg (fun α => ((α x).choose k : K)) F =
      monomial (Finsupp.single x k) 1 * ddiv (Finsupp.single x k) F := by
  rw [dg_eq_sum]
  unfold ddiv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs with h
  · have hk : k ≤ α x := Finsupp.single_le_iff.mp h
    rw [monomial_mul, add_tsub_cancel_of_le h, one_mul, prod_choose_single α x k hk, mul_comm]
  · have hk : α x < k := by
      by_contra hh
      exact h (Finsupp.single_le_iff.mpr (not_lt.mp hh))
    rw [Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, zero_mul, monomial_zero, mul_zero]

theorem vala_dg_choose (hV2 : V2 K) {θ : ℝ} (x : L × Fin r) (k : ℕ)
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S (θ - k) (dg (fun α => ((α x).choose k : K)) F) := by
  rw [dg_choose_eq]
  have hs : Finsupp.single x k = onLetter x.1 (Finsupp.single x.2 k) := by
    unfold onLetter
    rw [Finsupp.mapDomain_single]
  have habs : absE (Finsupp.single x.2 k) = k := by
    unfold absE
    rw [Finsupp.sum_single_index rfl]
  have h1 := vala_ddiv_letter' hV2 x.1 (Finsupp.single x.2 k) hF
  rw [← hs, habs] at h1
  have h2 : vala sg S (k * (if sg x.1 then 0 else -1 : ℝ))
      (monomial (Finsupp.single x k) (1 : K)) := by
    rw [← X_pow_eq_monomial]
    exact vala_pow (vala_X hV2 x.1 x.2) k
  have h3 := vala_mul h2 h1
  convert h3 using 1
  split_ifs <;> ring

end FromV2

section TotallyRealRoots

variable {K : Type} [Field K]

theorem dg_mul {σ : Type} (f g : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg (fun α => f α * g α) F = dg f (dg g F) := by
  ext β; simp only [coeff_dg]; ring

theorem dg_one {σ : Type} (F : MvPolynomial σ K) : dg (fun _ => (1 : K)) F = F := by
  ext β; simp only [coeff_dg, one_mul]

theorem dg_sum_smul {σ ι : Type} (s : Finset ι) (lam : ι → K) (b : ι → (σ →₀ ℕ) → K)
    (F : MvPolynomial σ K) :
    dg (fun α => ∑ k ∈ s, lam k * b k α) F = ∑ k ∈ s, lam k • dg (b k) F := by
  ext β
  simp only [coeff_dg, coeff_sum, coeff_smul, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem dg_congr {σ : Type} {f g : (σ →₀ ℕ) → K} {F : MvPolynomial σ K}
    (h : ∀ α ∈ F.support, f α = g α) : dg f F = dg g F := by
  ext β
  simp only [coeff_dg]
  by_cases hβ : β ∈ F.support
  · rw [h β hβ]
  · rw [notMem_support_iff.mp hβ, mul_zero, mul_zero]

theorem support_dg_subset_v {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    (dg f F).support ⊆ F.support := by
  intro β hβ
  rw [mem_support_iff, coeff_dg] at hβ
  rw [mem_support_iff]
  intro h0; apply hβ; rw [h0, mul_zero]

theorem dg_monomial_mul {σ : Type} (g : (σ →₀ ℕ) → K) (μ : σ →₀ ℕ) (Q : MvPolynomial σ K) :
    dg g (monomial μ 1 * Q) = monomial μ 1 * dg (fun β => g (μ + β)) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial β c => rw [monomial_mul, dg_monomial, dg_monomial, monomial_mul, one_mul, one_mul]
  | add p q hp hq => rw [mul_add, map_add, map_add, mul_add, hp, hq]

variable {L : Type} [DecidableEq L] {r : ℕ} {sg : L → Bool} {S : Finset L}

theorem valS_monomial_nonneg_of_free (μ : L × Fin r →₀ ℕ) (c : K) (h : ∀ i ∈ S, ∀ a, μ (i, a) = 0) :
    0 ≤ valS sg S (monomial μ c) := by
  classical
  refine valS_nonneg_of_free sg S _ fun α hα i hi a => ?_
  have : α = μ := by
    have := support_monomial_subset hα
    simpa using this
  rw [this]; exact h i hi a

theorem valS_monomial_nonneg_of_vec (μ : L × Fin r →₀ ℕ) (c : K)
    (h : ∀ i a, μ (i, a) ≠ 0 → sg i = true) : 0 ≤ valS sg S (monomial μ c) := by
  classical
  refine valS_nonneg_of_vec sg S _ fun α hα i a hne => ?_
  have : α = μ := by
    have := support_monomial_subset hα
    simpa using this
  rw [this] at hne; exact h i a hne

theorem vala_dg_outside (out : L → Prop) [DecidablePred out] (hout : ∀ i ∈ S, ¬ out i)
    (g : (L × Fin r →₀ ℕ) → K) (n θ : ℝ)
    (h : ∀ μ, eOut out μ = μ → ∀ G : MvPolynomial (L × Fin r) K, vala sg S θ G →
      vala sg S (θ - n) (dg (fun β => g (μ + β)) G))
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) : vala sg S (θ - n) (dg g F) := by
  conv => rw [sum_coefOut out F, map_sum]
  refine vala_sum _ _ fun μ hμ => ?_
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hμ
  rw [dg_monomial_mul]
  refine vala_mul_left_nonneg (valS_monomial_nonneg_of_free _ _ ?_)
    (h _ (eOut_eOut out α) _ (vala_coefOut out hout _ hF))
  intro i hi a
  rw [eOut_apply, if_neg (hout i hi)]

end TotallyRealRoots

end Formalism.MainNotions.PlaneGram

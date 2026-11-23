import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs

noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)] {K'' : Type} [Fintype K''] {ι'' : K'' → Type}
  [∀ b, Fintype (ι'' b)]

theorem vsup_ne_zero (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} {b : K} (h : ∃ i, y ⟨b, i⟩ ≠ 0) :
    (Finset.univ.sup fun i => O.valuation (y ⟨b, i⟩)) ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  intro h0
  have h1 : O.valuation (y ⟨b, i⟩) ≤ Finset.univ.sup fun i => O.valuation (y ⟨b, i⟩) :=
    Finset.le_sup (f := fun i => O.valuation (y ⟨b, i⟩)) (Finset.mem_univ i)
  rw [h0] at h1
  exact hi ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le))

theorem vdeg_ne_zero (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (a : K → ℤ) :
    vdeg O y a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (vsup_ne_zero O (h b))

@[simp] theorem vdeg_zero (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) : vdeg O y 0 = 1 := by simp [vdeg]

theorem vdeg_add (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (a a' : K → ℤ) :
    vdeg O y (a + a') = vdeg O y a * vdeg O y a' := by
  unfold vdeg
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun b _ => zpow_add₀ (vsup_ne_zero O (h b)) _ _

theorem vdeg_neg (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (a : K → ℤ) : vdeg O y (-a) = (vdeg O y a)⁻¹ := by
  unfold vdeg
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun b _ => zpow_neg _ _

theorem vdeg_sub (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (a a' : K → ℤ) :
    vdeg O y (a - a') = vdeg O y a / vdeg O y a' := by
  rw [sub_eq_add_neg, vdeg_add O h, vdeg_neg, div_eq_mul_inv]

theorem vdeg_sum (O : ValuationSubring Ω) {y : (Σ b, ι b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) {T : Type} (s : Finset T)
    (a : T → K → ℤ) : vdeg O y (∑ t ∈ s, a t) = ∏ t ∈ s, vdeg O y (a t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert t s ht ih => rw [Finset.sum_insert ht, Finset.prod_insert ht, vdeg_add O h, ih]

theorem vdeg_join (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a a') = vdeg O y a * vdeg O y' a' := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  rfl

theorem vdeg_join_inl (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a 0) = vdeg O y a := by rw [vdeg_join, vdeg_zero, mul_one]

theorem vdeg_join_inr (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim 0 a') = vdeg O y' a' := by rw [vdeg_join, vdeg_zero, one_mul]

theorem joinPt_ne {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} (h : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) :
    ∀ b, ∃ i, joinPt y y' ⟨b, i⟩ ≠ 0
  | .inl b => h b
  | .inr b => h' b

namespace ValEq

variable {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {y'' : (Σ b, ι'' b) → Ω}

theorem of_eq {a : K → ℤ} {a' : K' → ℤ} (h : ∀ O : ValuationSubring Ω, vdeg O y a = vdeg O y' a') : ValEq k y a y' a' :=
  ⟨1, one_ne_zero, fun O _ => by rw [h O, map_one, one_mul]⟩

theorem refl (y : (Σ b, ι b) → Ω) (a : K → ℤ) : ValEq k y a y a := of_eq fun _ => rfl

theorem zero (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) : ValEq k y 0 y' 0 := of_eq fun _ => by simp

theorem symm {a : K → ℤ} {a' : K' → ℤ} (h : ValEq k y a y' a') : ValEq k y' a' y a := by
  obtain ⟨ρ, h0, h⟩ := h
  refine ⟨ρ⁻¹, inv_ne_zero h0, fun O hO => ?_⟩
  rw [h O hO, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]

theorem trans {a : K → ℤ} {a' : K' → ℤ} {a'' : K'' → ℤ} (h : ValEq k y a y' a') (h' : ValEq k y' a' y'' a'') :
    ValEq k y a y'' a'' := by
  obtain ⟨ρ, h0, h⟩ := h
  obtain ⟨ρ', h0', h'⟩ := h'
  exact ⟨ρ * ρ', mul_ne_zero h0 h0', fun O hO => by rw [h O hO, h' O hO, map_mul, mul_assoc]⟩

theorem add (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (hy' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) {a b : K → ℤ} {a' b' : K' → ℤ}
    (h : ValEq k y a y' a') (h' : ValEq k y b y' b') : ValEq k y (a + b) y' (a' + b') := by
  obtain ⟨ρ, h0, h⟩ := h
  obtain ⟨ρ', h0', h'⟩ := h'
  refine ⟨ρ * ρ', mul_ne_zero h0 h0', fun O hO => ?_⟩
  rw [vdeg_add O hy, vdeg_add O hy', h O hO, h' O hO, map_mul, mul_mul_mul_comm]

theorem neg {a : K → ℤ} {a' : K' → ℤ} (h : ValEq k y a y' a') : ValEq k y (-a) y' (-a') := by
  obtain ⟨ρ, h0, h⟩ := h
  exact ⟨ρ⁻¹, inv_ne_zero h0, fun O hO => by rw [vdeg_neg, vdeg_neg, h O hO, map_inv₀, mul_inv]⟩

theorem sub (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (hy' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) {a b : K → ℤ} {a' b' : K' → ℤ}
    (h : ValEq k y a y' a') (h' : ValEq k y b y' b') : ValEq k y (a - b) y' (a' - b') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact add hy hy' h h'.neg

theorem sum (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (hy' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) {T : Type} (s : Finset T) {a : T → K → ℤ}
    {a' : T → K' → ℤ} (h : ∀ t ∈ s, ValEq k y (a t) y' (a' t)) : ValEq k y (∑ t ∈ s, a t) y' (∑ t ∈ s, a' t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero y y'
  | insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht]
    exact add hy hy' (h t (Finset.mem_insert_self _ _)) (ih fun t' ht' => h t' (Finset.mem_insert_of_mem ht'))

theorem join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) : ValEq k (joinPt y y') (Sum.elim a 0) y a :=
  of_eq fun O => vdeg_join_inl O y y' a

theorem join_inr (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) : ValEq k (joinPt y y') (Sum.elim 0 a') y' a' :=
  of_eq fun O => vdeg_join_inr O y y' a'

end ValEq

end SheetDecomposition

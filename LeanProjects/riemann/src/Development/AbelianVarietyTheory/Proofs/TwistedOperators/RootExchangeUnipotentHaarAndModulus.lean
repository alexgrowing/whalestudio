import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.VolN

section Alg
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

def lm (P : ι → ι → Prop) (h : Matrix ι ι k) :
    Matrix {rs : ι × ι // P rs.1 rs.2} {rs : ι × ι // P rs.1 rs.2} k :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then h a.1.1 b.1.1 else 0

def rm (P : ι → ι → Prop) (h : Matrix ι ι k) :
    Matrix {rs : ι × ι // P rs.1 rs.2} {rs : ι × ι // P rs.1 rs.2} k :=
  Matrix.of fun a b => if a.1.1 = b.1.1 then h b.1.2 a.1.2 else 0

def ext0 (P : ι → ι → Prop) [DecidableRel P] (e : {rs : ι × ι // P rs.1 rs.2} → k) : Matrix ι ι k :=
  Matrix.of fun r s => if h : P r s then e ⟨(r, s), h⟩ else 0

omit [DecidableEq ι] in
theorem sum_extendByZero_fin_eq_sum_of_eq (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}]
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (w : ι × ι → k) :
    ∑ b : {rs : ι × ι // P rs.1 rs.2}, w b.1 * e b = ∑ r, ∑ s, w (r, s) * ext0 P e r s := by
  rw [← Fintype.sum_prod_type' (fun r s => w (r, s) * ext0 P e r s),
    ← Finset.sum_filter_of_ne (p := fun rs : ι × ι => P rs.1 rs.2),
    Finset.sum_subtype (p := fun rs : ι × ι => P rs.1 rs.2) (F := F) _ (by simp)]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [ext0, b.2]
  · intro x _ hx
    by_contra h
    simp [ext0, h] at hx

theorem mul_matrixExtendSelectedEntriesByZero_apply (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k)
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (a : {rs : ι × ι // P rs.1 rs.2}) :
    (h * ext0 P e) a.1.1 a.1.2 = (lm P h).mulVec e a := by
  have := sum_extendByZero_fin_eq_sum_of_eq P e (fun b => if a.1.2 = b.2 then h a.1.1 b.1 else 0)
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, lm, Matrix.of_apply]
  rw [this]
  simp

theorem matrixExtendByZero_mul (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k)
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (a : {rs : ι × ι // P rs.1 rs.2}) :
    (ext0 P e * h) a.1.1 a.1.2 = (rm P h).mulVec e a := by
  have := sum_extendByZero_fin_eq_sum_of_eq P e (fun b => if a.1.1 = b.1 then h b.2 a.1.2 else 0)
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, rm, Matrix.of_apply]
  rw [this, Finset.sum_comm]
  simp [mul_comm]

theorem det_lm (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}]
    [DecidableEq {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k) :
    (lm P h).det = ∏ s, (h.toSquareBlockProp fun r => P r s).det := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have ht : (lm P h).BlockTriangular (fun a => a.1.2) := by
    intro a b hab
    simp only [lm, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab).symm]
  rw [ht.det_fintype]
  refine Finset.prod_congr rfl fun s _ => ?_
  let E : {r // P r s} ≃ {a : {rs : ι × ι // P rs.1 rs.2} // a.1.2 = s} :=
    { toFun := fun r => ⟨⟨(r.1, s), r.2⟩, rfl⟩
      invFun := fun a => ⟨a.1.1.1, by have h1 := a.1.2; have h2 : a.1.1.2 = s := a.2; rwa [h2] at h1⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨⟨r, s'⟩, h⟩, rfl⟩; rfl }
  rw [← Matrix.det_submatrix_equiv_self E]
  congr 1
  ext i j
  simp [toSquareBlock_def, toSquareBlockProp_def, lm, E]

theorem det_rm (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}]
    [DecidableEq {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k) :
    (rm P h).det = ∏ r, (h.toSquareBlockProp fun s => P r s).det := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have ht : (rm P h).BlockTriangular (fun a => a.1.1) := by
    intro a b hab
    simp only [rm, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab).symm]
  rw [ht.det_fintype]
  refine Finset.prod_congr rfl fun s _ => ?_
  let E : {r // P s r} ≃ {a : {rs : ι × ι // P rs.1 rs.2} // a.1.1 = s} :=
    { toFun := fun r => ⟨⟨(s, r.1), r.2⟩, rfl⟩
      invFun := fun a => ⟨a.1.1.2, by have h1 := a.1.2; have h2 : a.1.1.1 = s := a.2; rwa [h2] at h1⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨⟨r, s'⟩, h⟩, rfl⟩; rfl }
  rw [← Matrix.det_submatrix_equiv_self E, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [toSquareBlock_def, toSquareBlockProp_def, rm, E]

theorem det_unitri (b : ι → ℕ) (M : Matrix ι ι k)
    (hM : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have ht : M.BlockTriangular b := by
    intro r s h
    rw [hM r s h.le, Matrix.one_apply_ne]
    rintro rfl; exact lt_irrefl _ h
  rw [ht.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp [toSquareBlock_def, hM r s (by omega), Matrix.one_apply]
  rw [this, det_one]

theorem det_block_unitri (b : ι → ℕ) (M : Matrix ι ι k)
    (hM : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) (Q : ι → Prop) [DecidablePred Q] :
    (M.toSquareBlockProp Q).det = 1 := by
  refine det_unitri (fun r => b r.1) _ fun r s h => ?_
  simp [toSquareBlockProp_def, hM _ _ h, Matrix.one_apply, Subtype.ext_iff]

theorem det_block_fromBlocks {n t : Type} [Fintype n] [DecidableEq n] [Fintype t] [DecidableEq t]
    (x : Matrix n n k) (Q : n ⊕ t → Prop) [DecidablePred Q] (q : Prop) [Decidable q]
    (hQ : ∀ a, Q (Sum.inl a) ↔ q) :
    ((fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q).det = if q then x.det else 1 := by
  have key : ∀ (Q : n ⊕ t → Prop) [DecidablePred Q], (∀ a, ¬ Q (Sum.inl a)) →
      ((fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q).det = 1 := by
    intro Q _ hQ
    have : (fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q = 1 := by
      ext ⟨r | r, hr⟩ ⟨s | s, hs⟩
      · exact absurd hr (hQ _)
      · exact absurd hr (hQ _)
      · exact absurd hs (hQ _)
      · simp [toSquareBlockProp_def, Matrix.one_apply]
    rw [this, det_one]
  split_ifs with hq
  · have := Matrix.twoBlockTriangular_det (fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k) Q (by
      rintro (r | r) hr (s | s) hs
      · exact absurd ((hQ r).2 hq) hr
      · exact absurd ((hQ r).2 hq) hr
      · simp
      · have : r ≠ s := by rintro rfl; exact hr hs
        simp [this])
    rw [key (fun i => ¬ Q i) (fun a ha => ha ((hQ a).2 hq)), mul_one] at this
    rw [← this]; simp
  · exact key Q fun a ha => hq ((hQ a).1 ha)

end Alg

section Grp
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

abbrev Up (n : Type) (c p : ℕ) : n ⊕ Fin c → n ⊕ Fin c → Prop := fun r s => lev p r < lev p s

abbrev Ix (n : Type) (c p : ℕ) : Type := {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}

def co (p : ℕ) (g : N k n c p) : Ix n c p → k := fun rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2

theorem val_mkNel (p : ℕ) (e : Ix n c p → k) :
    ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k).val = 1 + ext0 (Up n c p) e := by
  ext r s
  change mkN p e r s = _
  by_cases h : lev p r < lev p s
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [mkN, ext0, h, this]
  · simp [mkN, ext0, h]

theorem co_mkNel (p : ℕ) (e : Ix n c p → k) : co p (mkNel p e) = e := by
  funext rs
  change mkN p e _ _ = _
  simp [mkN, rs.2]

theorem mkNel_co (p : ℕ) (g : N k n c p) : mkNel p (co p g) = g := by
  ext r s
  change mkN p (co p g) r s = _
  by_cases h : lev p r < lev p s
  · simp [mkN, h, co]
  · simp only [mkN, Matrix.of_apply, dif_neg h]
    exact (mem_N_iff.1 g.2 r s (not_lt.1 h)).symm

theorem mul_mkNel (p : ℕ) (g : N k n c p) (e : Ix n c p → k) :
    g * mkNel p e = mkNel p ((lm (Up n c p) (g : GL (n ⊕ Fin c) k).val).mulVec e + co p g) := by
  rw [← mkNel_co p (g * mkNel p e)]
  congr 1
  funext rs
  rw [Pi.add_apply, ← mul_matrixExtendSelectedEntriesByZero_apply]
  simp only [co, Subgroup.coe_mul, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  rw [add_comm]

theorem mkNel_mul (p : ℕ) (g : N k n c p) (e : Ix n c p → k) :
    mkNel p e * g = mkNel p ((rm (Up n c p) (g : GL (n ⊕ Fin c) k).val).mulVec e + co p g) := by
  rw [← mkNel_co p (mkNel p e * g)]
  congr 1
  funext rs
  rw [Pi.add_apply, ← matrixExtendByZero_mul]
  simp only [co, Subgroup.coe_mul, Units.val_mul, val_mkNel, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  rw [add_comm]

theorem det_lm_N (p : ℕ) (g : N k n c p) : (lm (Up n c p) (g : GL (n ⊕ Fin c) k).val).det = 1 := by
  rw [det_lm]
  exact Finset.prod_eq_one fun s _ => det_block_unitri (lev p) _ (mem_N_iff.1 g.2) _

theorem det_rm_N (p : ℕ) (g : N k n c p) : (rm (Up n c p) (g : GL (n ⊕ Fin c) k).val).det = 1 := by
  rw [det_rm]
  exact Finset.prod_eq_one fun s _ => det_block_unitri (lev p) _ (mem_N_iff.1 g.2) _

theorem val_embX (x : GL n k) : (embX c x).val = fromBlocks x.val 0 0 1 := rfl

theorem rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks (p : ℕ) (x : GL n k) (e : Ix n c p → k) :
    (embX c x).val * ext0 (Up n c p) e = ext0 (Up n c p) ((lm (Up n c p) (embX c x).val).mulVec e) := by
  ext r s
  by_cases h : lev p r < lev p s
  · rw [mul_matrixExtendSelectedEntriesByZero_apply (Up n c p) _ e ⟨(r, s), h⟩]
    simp [ext0, h]
  · have h0 : ∀ t, lev p t = lev p r → ∀ e : Ix n c p → k, ext0 (Up n c p) e t s = 0 := by
      intro t ht e
      simp only [ext0, Matrix.of_apply]
      rw [dif_neg]
      simpa [ht] using h
    rw [h0 r rfl, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    rcases r with r | r <;> rcases t with t | t
    · rw [h0 (Sum.inl t) rfl, mul_zero]
    · simp [val_embX]
    · simp [val_embX]
    · by_cases hrt : r = t
      · rw [h0 _ (by rw [hrt]), mul_zero]
      · simp [val_embX, hrt]

theorem conj_mkNel (p : ℕ) (x : GL n k) (e : Ix n c p → k) :
    embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹ =
      (mkNel p ((rm (Up n c p) (embX c x⁻¹).val * lm (Up n c p) (embX c x).val).mulVec e) : N k n c p) := by
  have hm : embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹ ∈ N k n c p := by
    simpa using conj_mem (mkNel p e).2 x⁻¹
  have := mkNel_co p ⟨_, hm⟩
  refine (congrArg Subtype.val this).symm.trans ?_
  congr 2
  funext rs
  rw [← Matrix.mulVec_mulVec, ← matrixExtendByZero_mul, ← rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks, map_inv]
  have hne : rs.1.1 ≠ rs.1.2 := fun h => by have := rs.2; rw [h] at this; exact lt_irrefl _ this
  simp only [co, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv,
    Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]

theorem det_lm_embX {p : ℕ} (x : GL n k) :
    (lm (Up n c p) (embX c x).val).det = x.val.det ^ (c - p) := by
  rw [det_lm, val_embX]
  rw [Finset.prod_congr rfl fun s _ => det_block_fromBlocks x.val _ (p < lev p s) fun a => Iff.rfl]
  rw [Fintype.prod_sum_type]
  change (∏ _a : n, if p < p then x.val.det else 1) * (∏ i : Fin c, if p < i.val + 1 then x.val.det else 1) = _
  simp only [lt_irrefl, if_false, Finset.prod_const_one, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => if p < i + 1 then x.val.det else 1), ← Finset.prod_filter,
    Finset.prod_const]
  congr 1
  have : (Finset.range c).filter (fun i => p < i + 1) = Finset.Ico p c := by
    ext i; simp; omega
  rw [this, Nat.card_Ico]

theorem det_rm_embX {p : ℕ} (hp : p ≤ c) (x : GL n k) :
    (rm (Up n c p) (embX c x).val).det = x.val.det ^ (p - 1) := by
  rw [det_rm, val_embX]
  rw [Finset.prod_congr rfl fun s _ => det_block_fromBlocks x.val _ (lev p s < p) fun a => Iff.rfl]
  rw [Fintype.prod_sum_type]
  change (∏ _a : n, if p < p then x.val.det else 1) * (∏ i : Fin c, if i.val + 1 < p then x.val.det else 1) = _
  simp only [lt_irrefl, if_false, Finset.prod_const_one, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => if i + 1 < p then x.val.det else 1), ← Finset.prod_filter,
    Finset.prod_const]
  congr 1
  have : (Finset.range c).filter (fun i => i + 1 < p) = Finset.range (p - 1) := by
    ext i; simp; omega
  rw [this, Finset.card_range]

def InR (p : ℕ) (g : GL (n ⊕ Fin c) k) : Prop :=
  ∀ r s, lev p s ≤ lev p r → (r.isRight ∨ s.isRight) → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s

theorem exists_of_mem_R {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ R k n c p) :
    ∃ x : GL n k, ∃ u ∈ N k n c p, g = embX c x * u := by
  let S : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {g | ∃ x : GL n k, ∃ u ∈ N k n c p, g = embX c x * u}
      one_mem' := ⟨1, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, u, hu, rfl⟩ ⟨y, v, hv, rfl⟩
        exact ⟨x * y, _, mul_mem (conj_mem hu y) hv, by simp [mul_assoc]⟩
      inv_mem' := by
        rintro _ ⟨x, u, hu, rfl⟩
        exact ⟨x⁻¹, _, conj_mem (inv_mem hu) x⁻¹, by simp [mul_assoc]⟩ }
  have : R k n c p ≤ S := sup_le (by rintro _ ⟨x, rfl⟩; exact ⟨x, 1, one_mem _, by simp⟩)
    fun u hu => ⟨1, u, hu, by simp⟩
  exact this hg

theorem inR_of_mem {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ R k n c p) : InR p g := by
  obtain ⟨x, u, hu, rfl⟩ := exists_of_mem_R hg
  rw [mem_N_iff] at hu
  rintro (r | r) (s | s) h h'
  · simp at h'
  · have : ∀ t, u.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
      simpa using hu (Sum.inl t) (Sum.inr s) h
    simp [val_embX, Matrix.mul_apply, this]
  · rw [← hu _ _ h]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
  · rw [← hu _ _ h]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]

theorem mem_R_iff {p : ℕ} {g : GL (n ⊕ Fin c) k} : g ∈ R k n c p ↔ InR p g ∧ InR p g⁻¹ := by
  refine ⟨fun h => ⟨inR_of_mem h, inR_of_mem (inv_mem h)⟩, fun ⟨h1, h2⟩ => ?_⟩
  have e : (g⁻¹).val.toBlocks₁₁ * g.val.toBlocks₁₁ = 1 := by
    ext a b
    have h3 := congrFun (congrFun g.inv_mul (Sum.inl a)) (Sum.inl b)
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h3
    have h4 : ∑ i : Fin c, (g⁻¹).val (Sum.inl a) (Sum.inr i) * g.val (Sum.inr i) (Sum.inl b) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases le_total (i.val + 1) p with hi | hi
      · rw [h2 (Sum.inl a) (Sum.inr i) hi (by simp)]; simp
      · rw [h1 (Sum.inr i) (Sum.inl b) hi (by simp)]; simp
    rw [h4, add_zero] at h3
    rw [Matrix.mul_apply]
    simpa [Matrix.one_apply, toBlocks₁₁] using h3
  let y : GL n k := ⟨_, _, e, mul_eq_one_comm.1 e⟩
  have hy : embX c y * g ∈ N k n c p := by
    rw [mem_N_iff]
    rintro (r | r) (s | s) h
    · have := congrFun (congrFun e r) s
      rw [Matrix.mul_apply] at this
      simpa [val_embX, Matrix.mul_apply, y, Matrix.one_apply, toBlocks₁₁] using this
    · have : ∀ t, g.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
        simpa using h1 (Sum.inl t) (Sum.inr s) h (by simp)
      simp [val_embX, Matrix.mul_apply, this]
    · rw [← h1 _ _ h (by simp)]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
    · rw [← h1 _ _ h (by simp)]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
  have : g = embX c y⁻¹ * (embX c y * g) := by simp
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right hy)

end Grp

section Meas
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem continuous_entry (r s : n) : Continuous fun g : GL n k => g.val r s := by
  have := Units.continuous_val (M := Matrix n n k)
  fun_prop

theorem isClosed_N (p : ℕ) : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  have := (SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have e : (N k n c p : Set (GL (n ⊕ Fin c) k)) = {g | InN p g} := Set.ext fun g => mem_N_iff
  rw [e]
  simp only [InN, Set.ofPred_forall]
  exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_eq (continuous_entry r s) continuous_const

theorem isClosed_R (p : ℕ) : IsClosed (R k n c p : Set (GL (n ⊕ Fin c) k)) := by
  have := (SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have h : IsClosed {g : GL (n ⊕ Fin c) k | InR p g} := by
    simp only [InR, Set.ofPred_forall]
    exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_entry r s) continuous_const
  have e : (R k n c p : Set (GL (n ⊕ Fin c) k)) = {g | InR p g} ∩ (fun g => g⁻¹) ⁻¹' {g | InR p g} :=
    Set.ext fun g => mem_R_iff
  rw [e]
  exact h.inter (h.preimage continuous_inv)

theorem continuous_co (p : ℕ) : Continuous (co (k := k) (n := n) (c := c) p) :=
  continuous_pi fun rs => (continuous_entry rs.1.1 rs.1.2).comp continuous_subtype_val

theorem continuous_mkNel (p : ℕ) : Continuous (mkNel (k := k) (n := n) (c := c) p) := by
  have h1 : Continuous (mkN (k := k) (n := n) (c := c) p) := by
    refine continuous_pi fun r => continuous_pi fun s => ?_
    by_cases h : lev p r < lev p s
    · simp only [mkN, Matrix.of_apply, dif_pos h]; exact continuous_apply _
    · simp only [mkN, Matrix.of_apply, dif_neg h]; exact continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨h1.congr fun _ => rfl, ?_⟩)
  refine h1.matrix_adjugate.congr fun e => ?_
  rw [Matrix.coe_units_inv, Matrix.inv_def]
  change _ = Ring.inverse (mkN p e).det • (mkN p e).adjugate
  rw [det_mkN]; simp

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem map_affine {a : Type} [Fintype a] [DecidableEq a] (L : Matrix a a k) (hL : L.det = 1) (b : a → k) :
    Measurable (fun e => L.mulVec e + b) ∧
      (Measure.pi fun _ : a => ν).map (fun e => L.mulVec e + b) = Measure.pi fun _ : a => ν := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let g : GL a k := Matrix.GeneralLinearGroup.mkOfDetNeZero L (hL ▸ one_ne_zero)
  have hg : Matrix.GeneralLinearGroup.det g = 1 := Units.ext hL
  have hc : ∀ M : Matrix a a k, Continuous fun e => M.mulVec e := fun M =>
    continuous_const.matrix_mulVec continuous_id
  let T : (a → k) ≃ₜ (a → k) :=
    { toFun := fun e => g.val.mulVec e
      invFun := fun e => (g⁻¹).val.mulVec e
      left_inv := fun e => by simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      right_inv := fun e => by simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  have h1 : (Measure.pi fun _ : a => ν).map T = Measure.pi fun _ : a => ν := by
    have := Measure.Regular.map (μ := Measure.pi fun _ : a => ν) T
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
    have h2 := integral_comp_mulVec_eq_smul ν g fun x => (f x : ℂ)
    rw [hg, integral_complex_ofReal, integral_complex_ofReal] at h2
    have h3 := integral_map_equiv (μ := Measure.pi fun _ : a => ν) T.toMeasurableEquiv f
    rw [Homeomorph.toMeasurableEquiv_coe] at h3
    rw [h3]
    change ∫ x, f (g.val.mulVec x) ∂_ = _
    simpa [nabs] using h2
  refine ⟨((hc L).add continuous_const).measurable, ?_⟩
  have : (fun e => L.mulVec e + b) = (fun e => e + b) ∘ T := rfl
  rw [this, ← Measure.map_map (measurable_add_const b) T.continuous.measurable, h1, map_add_right_eq_self]

def coEquiv (p : ℕ) : (Ix n c p → k) ≃ᵐ N k n c p where
  toFun := mkNel p
  invFun := co p
  left_inv := co_mkNel p
  right_inv := mkNel_co p
  measurable_toFun := by
    have h := (coord_embedding (k := k) (n := n) (c := c) p).1
    refine (h.measurable_comp_iff).1 ?_
    have : (co (k := k) (n := n) (c := c) p) ∘ mkNel p = id := funext (co_mkNel p)
    exact this ▸ measurable_id
  measurable_invFun := (coord_embedding (k := k) (n := n) (c := c) p).1.measurable

theorem volN_eq (p : ℕ) : volN ν n c p = (Measure.pi fun _ : Ix n c p => ν).map (coEquiv p) := by
  rw [← MeasurableEquiv.comap_symm]
  unfold volN
  congr!

theorem map_volN_of_affine (p : ℕ) (T : N k n c p → N k n c p) (L : Matrix (Ix n c p) (Ix n c p) k)
    (hL : L.det = 1) (b : Ix n c p → k) (hT : ∀ e, T (mkNel p e) = mkNel p (L.mulVec e + b)) :
    (volN ν n c p).map T = volN ν n c p := by
  obtain ⟨h1, h2⟩ := map_affine ν L hL b
  have e1 : T ∘ coEquiv p = coEquiv p ∘ fun e => L.mulVec e + b := funext hT
  have e2 : T = coEquiv p ∘ (fun e => L.mulVec e + b) ∘ (coEquiv p).symm := by
    rw [← Function.comp_assoc, ← e1]; ext1 g; simp
  have hm : Measurable T := e2 ▸ (coEquiv p).measurable.comp (h1.comp (coEquiv p).symm.measurable)
  rw [volN_eq, Measure.map_map hm (coEquiv p).measurable, e1, ← Measure.map_map (coEquiv p).measurable h1, h2]

theorem isHaarMeasure_volN (p : ℕ) : (volN ν n c p).IsHaarMeasure := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine { lt_top_of_isCompact := fun K hK => ?_, map_mul_left_eq_self := fun g => ?_, open_pos := fun U hU hne => ?_ }
  · rw [volN_eq, MeasurableEquiv.map_apply, ← MeasurableEquiv.image_symm]
    exact (hK.image (continuous_co p)).measure_lt_top
  · exact map_volN_of_affine ν p _ _ (det_lm_N p g) _ (mul_mkNel p g)
  · rw [volN_eq, MeasurableEquiv.map_apply]
    obtain ⟨g, hg⟩ := hne
    exact (hU.preimage (continuous_mkNel p)).measure_ne_zero _ ⟨co p g, by simpa [mkNel_co] using hg⟩

theorem isMulRightInvariant_volN (p : ℕ) : (volN ν n c p).IsMulRightInvariant :=
  ⟨fun g => map_volN_of_affine ν p _ _ (det_rm_N p g) _ (mkNel_mul p g)⟩

theorem integral_conj_volN {p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) =
      (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) •
        ∫ u : N k n c p, f u ∂(volN ν n c p) := by
  let d : kˣ := Matrix.GeneralLinearGroup.det x
  let u : kˣ := d⁻¹ ^ (p - 1) * d ^ (c - p)
  have hu : (rm (Up n c p) (embX c x⁻¹).val * lm (Up n c p) (embX c x).val).det = (u : k) := by
    rw [det_mul, det_lm_embX, det_rm_embX hp]; simp [u, d]
  let G : GL (Ix n c p) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hu ▸ u.ne_zero)
  have hG : Matrix.GeneralLinearGroup.det G = u := Units.ext hu
  have key := integral_comp_mulVec_eq_smul ν G (fun e => f (mkNel p e : N k n c p))
  rw [volN_eq, integral_map_equiv, integral_map_equiv]
  change ∫ e, f (embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂_ = _
  simp_rw [conj_mkNel]
  refine key.trans ?_
  rw [hG]
  congr 1
  have hd := nabs_pos' d
  have : nabs k u = (nabs k d)⁻¹ ^ (p - 1) * nabs k d ^ (c - p) := by simp [u, nabs]
  rw [this, mul_inv, inv_pow, inv_inv, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hd.le,
    ← Real.rpow_add hd, Nat.cast_sub h1, Nat.cast_sub hp]
  congr 1
  push_cast; ring

end Meas

theorem volN_haar_and_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure], IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) ∧ IsClosed (R k n c p : Set (GL (n ⊕ Fin c) k)) ∧ (volN ν n c p).IsHaarMeasure ∧ (volN ν n c p).IsMulRightInvariant ∧ ∀ (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ), ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) = (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) • ∫ u : N k n c p, f u ∂(volN ν n c p) :=
  fun _ _ _ _ _ _ _ _ _ _ _ p h1 hp ν _ =>
    ⟨isClosed_N p, isClosed_R p, isHaarMeasure_volN ν p, isMulRightInvariant_volN ν p,
      integral_conj_volN ν h1 hp⟩

end GlobalTheory.RootEx.VolN

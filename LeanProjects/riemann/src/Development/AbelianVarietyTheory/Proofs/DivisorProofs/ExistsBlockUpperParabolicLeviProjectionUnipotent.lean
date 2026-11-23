import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSuppor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.LeviHoms

variable {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)

def ix : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)

theorem ix_inl_val (x : Fin a) : ((ix h (Sum.inl x) : Fin n) : ℕ) = x := by simp [ix]

theorem ix_inr_val (x : Fin b) : ((ix h (Sum.inr x) : Fin n) : ℕ) = a + x := by simp [ix]

theorem ext_ix {R : Type} {M N : Matrix (Fin n) (Fin n) R}
    (H : ∀ P Q, M (ix h P) (ix h Q) = N (ix h P) (ix h Q)) : M = N := by
  ext i j
  obtain ⟨P, rfl⟩ := (ix h).surjective i
  obtain ⟨Q, rfl⟩ := (ix h).surjective j
  exact H P Q

theorem mem_parabolic_iff (g : GLw n w) :
    g ∈ parP a n w ↔ ∀ i j, g.val (ix h (Sum.inr i)) (ix h (Sum.inl j)) = 0 := by
  constructor
  · intro hg i j
    apply hg
    have h1 : ¬ a ≤ (j : ℕ) := Nat.not_le.2 j.isLt
    simp only [ix_inl_val, ix_inr_val]
    simp [h1]
  · intro H i j hij
    obtain ⟨P, rfl⟩ := (ix h).surjective i
    obtain ⟨Q, rfl⟩ := (ix h).surjective j
    rcases P with x | x <;> rcases Q with y | y
    · have h1 : ¬ a ≤ (x : ℕ) := Nat.not_le.2 x.isLt
      simp only [ix_inl_val] at hij
      simp [h1] at hij
      exact absurd hij (by cases decide (a ≤ (y : ℕ)) <;> decide)
    · simp only [ix_inl_val, ix_inr_val] at hij
      simp at hij
      exact absurd hij (by cases decide (a ≤ (x : ℕ)) <;> decide)
    · exact H x y
    · simp only [ix_inr_val] at hij
      simp at hij

theorem blk_apply (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (P Q : Fin a ⊕ Fin b) :
    (blk h w m X).val (ix h P) (ix h Q) = Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val P Q := by
  rw [UnipMean.blk_val]
  simp [ix]

theorem toBlocks₁₁_mul {R α β : Type} [CommRing R] [Fintype α] [Fintype β] (M N : Matrix (α ⊕ β) (α ⊕ β) R)
    (hN : N.toBlocks₂₁ = 0) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j
  have := fun y => congrFun (congrFun hN y) j
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, this]

theorem toBlocks₂₂_mul {R α β : Type} [CommRing R] [Fintype α] [Fintype β] (M N : Matrix (α ⊕ β) (α ⊕ β) R)
    (hM : M.toBlocks₂₁ = 0) : (M * N).toBlocks₂₂ = M.toBlocks₂₂ * N.toBlocks₂₂ := by
  ext i j
  have := fun y => congrFun (congrFun hM i) y
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type, this]

theorem toBlocks₂₁_of_mem (p : parP a n w) :
    ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₂₁ = 0 := by
  exact Matrix.ext fun i j => (mem_parabolic_iff h w _).1 p.2 i j

def dgH : parP a n w →* Matrix (Fin a) (Fin a) (w.adicCompletion E) × Matrix (Fin b) (Fin b) (w.adicCompletion E) where
  toFun p := (((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₁₁, ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₂₂)
  map_one' := by
    refine Prod.ext (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_) <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.one_apply]
  map_mul' p q := by
    have e : ((p * q : parP a n w) : GLw n w).val.submatrix (ix h) (ix h) =
        (p : GLw n w).val.submatrix (ix h) (ix h) * (q : GLw n w).val.submatrix (ix h) (ix h) := by
      rw [Matrix.submatrix_mul_equiv]; rfl
    simp only [e, Prod.mk_mul_mk]
    rw [toBlocks₁₁_mul _ _ (toBlocks₂₁_of_mem h w q), toBlocks₂₂_mul _ _ (toBlocks₂₁_of_mem h w p)]

def sH : GLw a w × GLw b w →* parP a n w where
  toFun m := ⟨blk h w m 0, (mem_parabolic_iff h w _).2 fun i j => by rw [blk_apply]; rfl⟩
  map_one' := Subtype.ext (UnipMean.blk_one_zero h w)
  map_mul' m m' := by
    apply Subtype.ext
    ext1
    simp only [Subgroup.coe_mul, Units.val_mul, UnipMean.blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add]

def piH : parP a n w →* GLw a w × GLw b w :=
  MulEquiv.prodUnits.toMonoidHom.comp ((Units.map (dgH h w)).comp (toUnits : parP a n w ≃* (parP a n w)ˣ).toMonoidHom)

theorem piH_fst_val (p : parP a n w) :
    ((piH h w p).1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) =
      ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₁₁ := rfl

theorem piH_snd_val (p : parP a n w) :
    ((piH h w p).2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) =
      ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₂₂ := rfl

def uH : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* parP a n w where
  toFun X := ⟨blk h w 1 (Multiplicative.toAdd X), (mem_parabolic_iff h w _).2 fun i j => by rw [blk_apply]; rfl⟩
  map_one' := Subtype.ext (UnipMean.blk_one_zero h w)
  map_mul' X Y := Subtype.ext (by simp only [toAdd_mul, Subgroup.coe_mul]; exact UnipMean.blk_add h w 1 _ _)

theorem piH_sH (m : GLw a w × GLw b w) : piH h w (sH h w m) = m := by
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · rw [piH_fst_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₁₁, sH, blk_apply]
  · rw [piH_snd_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₂₂, sH, blk_apply]

theorem uH_injective : Function.Injective (uH h w) := by
  intro X Y hXY
  have := congrArg (fun p : parP a n w => UnipMean.corner h w 1 (p : GLw n w)) hXY
  simpa [uH, UnipMean.corner_blk] using this

theorem piH_eq_one_iff (p : parP a n w) : piH h w p = 1 ↔ ∃ X, uH h w X = p := by
  constructor
  · intro hp
    have h1 := congrArg (fun q : GLw a w × GLw b w => (q.1 : Matrix (Fin a) (Fin a) (w.adicCompletion E))) hp
    have h2 := congrArg (fun q : GLw a w × GLw b w => (q.2 : Matrix (Fin b) (Fin b) (w.adicCompletion E))) hp
    simp only [piH_fst_val, piH_snd_val, Prod.fst_one, Prod.snd_one, Units.val_one] at h1 h2
    refine ⟨Multiplicative.ofAdd ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₁₂, ?_⟩
    apply Subtype.ext; ext1
    refine ext_ix h fun P Q => ?_
    simp only [uH, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [blk_apply]
    rcases P with x | x <;> rcases Q with y | y
    · have := congrFun (congrFun h1 x) y
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply] at this
      simp [this]
    · simp [Matrix.toBlocks₁₂]
    · simp [(mem_parabolic_iff h w _).1 p.2 x y]
    · have := congrFun (congrFun h2 x) y
      simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply] at this
      simp [this]
  · rintro ⟨X, rfl⟩
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [piH_fst_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₁₁, uH, blk_apply]
    · rw [piH_snd_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₂₂, uH, blk_apply]

theorem mem_intMat_iff (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    X ∈ intMat a b w ↔ ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1 := by
  let T : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :=
    { carrier := {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}
      one_mem' := fun i j => by simp
      mul_mem' := fun {x y} hx hy i j => by
        simp only [Set.mem_setOf_eq, toAdd_mul, Matrix.add_apply] at *
        exact Valuation.map_add_le _ (hx i j) (hy i j)
      inv_mem' := fun {x} hx i j => by
        simp only [Set.mem_setOf_eq, toAdd_inv, Matrix.neg_apply, Valuation.map_neg] at *
        exact hx i j }
  have e : intMat a b w = T :=
    le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx) fun x hx => Subgroup.subset_closure hx
  rw [e]
  rfl

theorem ent_iff {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)} :
    (∀ i j, Valued.v (M i j) ≤ 1) ↔ ∀ P Q, Valued.v (M (ix h P) (ix h Q)) ≤ 1 := by
  constructor
  · intro H P Q; exact H _ _
  · intro H i j
    obtain ⟨P, rfl⟩ := (ix h).surjective i
    obtain ⟨Q, rfl⟩ := (ix h).surjective j
    exact H P Q

theorem one_ent {k : Type} [Fintype k] [DecidableEq k] (i j : k) :
    Valued.v ((1 : Matrix k k (w.adicCompletion E)) i j) ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem blk_ent (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (H1 : ∀ i j, Valued.v (m.1.val i j) ≤ 1) (H2 : ∀ i j, Valued.v (m.2.val i j) ≤ 1)
    (HX : ∀ i j, Valued.v ((m.1.val * X) i j) ≤ 1) : ∀ i j, Valued.v ((blk h w m X).val i j) ≤ 1 := by
  rw [ent_iff h w]
  intro P Q
  rw [blk_apply]
  rcases P with x | x <;> rcases Q with y | y
  · simpa using H1 x y
  · simpa using HX x y
  · simp
  · simpa using H2 x y

theorem sH_mem (k : GLw a w × GLw b w) (hk : k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) :
    sH h w k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (parP a n w) := by
  rw [Subgroup.mem_subgroupOf, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  rw [Subgroup.mem_prod, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val] at hk
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hk
  refine ⟨blk_ent h w k 0 a1 b1 (by simp), ?_⟩
  have e : ((sH h w k : GLw n w))⁻¹ = (sH h w k⁻¹ : GLw n w) := by rw [map_inv]; rfl
  rw [e]
  exact blk_ent h w k⁻¹ 0 a2 b2 (by simp)

theorem piH_mem (k : parP a n w) (hk : k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (parP a n w)) :
    piH h w k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
  rw [Subgroup.mem_subgroupOf, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val] at hk
  obtain ⟨k1, k2⟩ := hk
  have e : (piH h w k)⁻¹ = piH h w k⁻¹ := (map_inv _ _).symm
  rw [Subgroup.mem_prod, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_, fun i j => ?_⟩
  · rw [piH_fst_val]; exact k1 (ix h (Sum.inl i)) (ix h (Sum.inl j))
  · rw [← Prod.fst_inv, e, piH_fst_val]; exact k2 (ix h (Sum.inl i)) (ix h (Sum.inl j))
  · rw [piH_snd_val]; exact k1 (ix h (Sum.inr i)) (ix h (Sum.inr j))
  · rw [← Prod.snd_inv, e, piH_snd_val]; exact k2 (ix h (Sum.inr i)) (ix h (Sum.inr j))

theorem uH_mem_iff (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    uH h w X ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (parP a n w) ↔ X ∈ intMat a b w := by
  rw [mem_intMat_iff, Subgroup.mem_subgroupOf, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  constructor
  · rintro ⟨H, -⟩ i j
    have := H (ix h (Sum.inl i)) (ix h (Sum.inr j))
    simpa [uH, blk_apply] using this
  · intro H
    have e : ((uH h w X : GLw n w))⁻¹ = (uH h w X⁻¹ : GLw n w) := by rw [map_inv]; rfl
    rw [e]
    refine ⟨blk_ent h w 1 _ (fun i j => by simpa using one_ent w i j) (fun i j => by simpa using one_ent w i j)
      (by simpa using H), blk_ent h w 1 _ (fun i j => by simpa using one_ent w i j)
      (fun i j => by simpa using one_ent w i j) (by simpa using H)⟩

end GlobalTheory.LeviDesc.LeviHoms

namespace GlobalTheory.LeviDesc.LeviHoms

theorem levi_homs : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E), ∃ (s : GLw a w × GLw b w →* GlobalTheory.LeviDesc.parP a n w) (π : GlobalTheory.LeviDesc.parP a n w →* GLw a w × GLw b w) (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* GlobalTheory.LeviDesc.parP a n w), (∀ m, (s m : GLw n w) = blk h w m 0) ∧ (∀ X, (u X : GLw n w) = blk h w 1 (Multiplicative.toAdd X)) ∧ (∀ m, π (s m) = m) ∧ Function.Injective u ∧ (∀ p, π p = 1 ↔ ∃ X, u X = p) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b), s k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w), π k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ∧ (∀ X, u X ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w) ↔ X ∈ intMat a b w) := by
  intro E _ _ n a b h w
  exact ⟨sH h w, piH h w, uH h w, fun m => rfl, fun X => rfl, piH_sH h w, uH_injective h w, piH_eq_one_iff h w,
    fun k hk => sH_mem h w k hk, fun k hk => piH_mem h w k hk, uH_mem_iff h w⟩

end GlobalTheory.LeviDesc.LeviHoms

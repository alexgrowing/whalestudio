import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.UnipMean

section Generic

variable {G : Type} [Group G]

def core (K K' : Subgroup G) : Subgroup G where
  carrier := {c | ∀ k ∈ K, k⁻¹ * c * k ∈ K'}
  one_mem' := by intro k _; simp
  mul_mem' := by
    intro a b ha hb k hk
    have : k⁻¹ * (a * b) * k = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by group
    rw [this]; exact K'.mul_mem (ha k hk) (hb k hk)
  inv_mem' := by
    intro a ha k hk
    have : k⁻¹ * a⁻¹ * k = (k⁻¹ * a * k)⁻¹ := by group
    rw [this]; exact K'.inv_mem (ha k hk)

theorem isOpen_core [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) : IsOpen (core K K' : Set G) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (1 : G)) (P := fun c k => k⁻¹ * c * k ∈ K') ?_
  · exact h
  intro k _
  have hc : Continuous fun p : G × G => p.2⁻¹ * p.1 * p.2 := by fun_prop
  have h1 : (fun p : G × G => p.2⁻¹ * p.1 * p.2) (1, k) ∈ (K' : Set G) := by simp [K'.one_mem]
  exact hc.continuousAt.preimage_mem_nhds (hK'.mem_nhds h1)

theorem cavg_mul_core (K K' : Subgroup G) (f : G → ℂ) (hf : ∀ k ∈ K', ∀ x, f (x * k) = f x) (x c : G)
    (hc : c ∈ core K K') : cavg K f (x * c) = cavg K f x := by
  unfold cavg
  congr 1
  funext k
  have := hf _ (hc k k.2) ((k : G)⁻¹ * x * k)
  rw [← this]
  congr 1
  group

theorem exists_of_cavg_ne_zero (K : Subgroup G) (f : G → ℂ) (x : G) (h : cavg K f x ≠ 0) :
    ∃ k ∈ K, f (k⁻¹ * x * k) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  unfold cavg avg
  have : (fun k : K => f ((k : G)⁻¹ * x * k)) = fun _ => 0 := funext fun k => hn k k.2
  rw [this]
  simp

end Generic

section Block

variable {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)

theorem isUnit_blkMat (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)

theorem blk_val (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  unfold blk
  simp only
  rw [dif_pos (isUnit_blkMat h w m X)]
  rfl

theorem blk_add (m : GLw a w × GLw b w) (x y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m (x + y) = blk h w m x * blk h w 1 y := by
  ext1
  rw [Units.val_mul, blk_val, blk_val, blk_val]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Prod.fst_one,
    Prod.snd_one, Units.val_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_add]
  congr 2
  exact add_comm _ _

theorem blk_one_zero : blk h w (1 : GLw a w × GLw b w) 0 = 1 := by
  ext1
  rw [blk_val]
  simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.mul_zero, Matrix.fromBlocks_one, Units.val_one]
  exact Matrix.submatrix_one_equiv _

theorem blk_one_neg (y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 y)⁻¹ = blk h w 1 (-y) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← blk_add, add_neg_cancel, blk_one_zero]

theorem continuous_blk_one : Continuous fun y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => blk h w 1 y := by
  have hv : Continuous fun y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (blk h w 1 y).val := by
    simp only [blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.one_mul]
    exact (continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_reindex _ _
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  simp only [blk_one_neg]
  exact hv.comp continuous_neg

def corner (m : GLw a w × GLw b w) (g : GLw n w) : Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
  (m.1⁻¹).val * (Matrix.reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm
    g.val).toBlocks₁₂

theorem corner_blk (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    corner h w m (blk h w m X) = X := by
  rw [corner, blk_val, ← Matrix.reindex_symm, Equiv.symm_apply_apply, Matrix.toBlocks_fromBlocks₁₂,
    ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem continuous_corner (m : GLw a w × GLw b w) : Continuous (corner h w m) := by
  unfold corner
  refine continuous_const.matrix_mul ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (Units.continuous_val.matrix_elem _ _)

end Block

theorem cavg_blk_locConst_compactSupport : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (blk h w m (x + y)) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (blk h w m x)) ∧ HasCompactSupport (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (blk h w m X)) := by
  intro E _ _ n a b h w f ⟨K', hK'o, hf⟩ m
  obtain ⟨_, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hCo : IsOpen (core (GlobalTheory.LFun.KGL w n) K' : Set (GLw n w)) := isOpen_core _ _ hKc hK'o
  let U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    { carrier := {y | blk h w 1 y ∈ core (GlobalTheory.LFun.KGL w n) K'}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, blk_one_zero]
        exact Subgroup.one_mem _
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [blk_add]
        exact Subgroup.mul_mem _ hx hy
      neg_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        rw [← blk_one_neg]
        exact Subgroup.inv_mem _ hx }
  refine ⟨⟨U, hCo.preimage (continuous_blk_one h w), fun x y hy => ?_⟩, ?_⟩
  · rw [blk_add]
    exact cavg_mul_core _ _ f (fun k hk x => (hf.2 k hk x).2) _ _ hy
  · let S : Set (GLw n w) := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * p.2.2) ''
      ((GlobalTheory.LFun.KGL w n : Set (GLw n w)) ×ˢ (tsupport f ×ˢ (GlobalTheory.LFun.KGL w n : Set (GLw n w))))
    have hS : IsCompact S := (hKc.prod (hf.1.isCompact.prod hKc)).image (by fun_prop)
    refine HasCompactSupport.intro (hS.image (continuous_corner h w m)) fun X hX => ?_
    by_contra hne
    obtain ⟨k, hk, hfk⟩ := exists_of_cavg_ne_zero _ f _ hne
    refine hX ⟨blk h w m X, ⟨(k, k⁻¹ * blk h w m X * k, k⁻¹),
      ⟨hk, subset_tsupport _ hfk, Subgroup.inv_mem _ hk⟩, by group⟩, corner_blk h w m X⟩

end GlobalTheory.LeviDesc.UnipMean

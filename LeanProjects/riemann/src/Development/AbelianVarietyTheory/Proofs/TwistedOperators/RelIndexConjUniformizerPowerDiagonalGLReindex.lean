import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.ReindexTorus

def reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') : GL n k ≃* GL n' k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k σ).toMulEquiv

theorem val_reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') (g : GL n k) : (reindexGL k σ g).val = Matrix.reindex σ σ g.val := rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem map_reindexGL_KO (σ : n ≃ n') : (KO k n).map (reindexGL k σ).toMonoidHom = KO k n' := by
  ext x
  rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff]
  have h1 : ∀ i j, ((reindexGL k σ).symm x).val i j = x.val (σ i) (σ j) := fun i j => rfl
  have h2 : ∀ i j, (((reindexGL k σ).symm x)⁻¹).val i j = (x⁻¹).val (σ i) (σ j) := fun i j => by
    rw [← map_inv]; rfl
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, h1, h2]
  exact and_congr ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩
    ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩

theorem reindexGL_torusElt (σ : n ≃ n') (ϖ : kˣ) (e : n → ℤ) :
    reindexGL k σ (torusElt k n ϖ e) = torusElt k n' ϖ (e ∘ σ.symm) := by
  refine Units.ext ?_
  rw [val_reindexGL, val_torusElt, val_torusElt, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  rfl

theorem relIndex_conj_torusElt_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n ≃ n') (e : n → ℤ),
    ((KO k n').map (MulAut.conj (torusElt k n' ϖ (e ∘ σ.symm))).toMonoidHom).relIndex (KO k n') =
      ((KO k n).map (MulAut.conj (torusElt k n ϖ e)).toMonoidHom).relIndex (KO k n) := by
  intro k _ _ _ _ ϖ n n' _ _ _ _ σ e
  set φ := reindexGL k σ
  have hconj : ∀ g : GL n k, ∀ H : Subgroup (GL n k),
      (H.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
        (H.map φ.toMonoidHom).map (MulAut.conj (φ g)).toMonoidHom := by
    intro g H
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x : 1
    simp [φ, map_mul, map_inv]
  have hK := map_reindexGL_KO k σ
  rw [← reindexGL_torusElt k σ ϖ e, ← hK, ← hconj]
  have key : ∀ A B : Subgroup (GL n k), (A.map φ.toMonoidHom).relIndex (B.map φ.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.map_equiv_eq_comap_symm' φ A, Subgroup.relIndex_comap, Subgroup.map_map]
    have : (φ.symm.toMonoidHom.comp φ.toMonoidHom) = MonoidHom.id _ := by ext x : 1; simp
    rw [this, Subgroup.map_id]
  exact key _ _

end GlobalTheory.ReindexTorus

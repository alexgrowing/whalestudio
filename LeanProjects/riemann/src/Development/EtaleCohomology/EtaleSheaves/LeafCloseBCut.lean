import Development.EtaleCohomology.EtaleSheaves.LeafSpreadVCut

noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafCloseBCut

def LeafProjModel : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A))

def LeafDimOpen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (b : X ⟶ Sp k) [LocallyOfFiniteType b],
    IsIntegral X → ∀ U : Set X, IsOpen U → U.Nonempty → topologicalKrullDim X ≤ topologicalKrullDim U

theorem goal_of (h1 : LeafProjModel) (h2 : LeafDimOpen) : LateralTheory.E.LeafSpreadVCut.LeafCloseB := by
  intro k _ A _ _ _ _
  obtain ⟨B, b, ι, hB, hb, hι, hc⟩ := h1 k A
  refine ⟨B, b, ι, hB, hb, hι, hc, ?_⟩
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum A) := inferInstance
  have hemb := ι.isOpenEmbedding
  calc topologicalKrullDim B ≤ topologicalKrullDim (Set.range ι) :=
        h2 k b hB _ hemb.isOpen_range ⟨ι x, x, rfl⟩
    _ = topologicalKrullDim (Sp A) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (hemb.isEmbedding.toHomeomorph).isHomeomorph).symm
    _ = ringKrullDim A := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

end LateralTheory.E.LeafCloseBCut

end

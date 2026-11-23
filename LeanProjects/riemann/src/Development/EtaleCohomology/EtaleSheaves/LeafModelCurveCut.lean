import Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafModelCurveCut

def ExistsNormalProperCurveModel : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L),
      IsIntegral C0 ∧ IsProper c0 ∧ (∀ y : C0, IsIntegrallyClosed (C0.presheaf.stalk y)) ∧
      topologicalKrullDim C0 = 1 ∧ IsGenericPoint x (⊤ : Set C0) ∧
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafSmoothOfNormal : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

theorem goal_of (hN : ExistsNormalProperCurveModel) (hS : LeafSmoothOfNormal) : LateralTheory.E.LeafCurveVCut.LeafModelCurve := by
  intro Ω L _ _ _ _ u hu hfin
  obtain ⟨C0, c0, x, ψ, hint, hprop, hnorm, hdim, hx, hψ⟩ := hN Ω L u hu hfin
  refine ⟨C0, c0, x, ψ, ⟨hint, hprop, ?_⟩, hx, hψ⟩
  have := hprop
  exact hS Ω c0 hint inferInstance hnorm hdim

end LateralTheory.E.LeafModelCurveCut

end

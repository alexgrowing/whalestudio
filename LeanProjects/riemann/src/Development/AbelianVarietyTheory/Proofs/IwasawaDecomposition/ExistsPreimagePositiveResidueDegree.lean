import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArithmeticVarietyDimZeroFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency.types false in

theorem exists_residueDegree_pos_of_mem_range (W Z : Scheme.{0}) (g : W ⟶ Z) [QuasiCompact g]
    [LocallyOfFiniteType g] (z : Z) (hz : z ∈ Set.range g) :
    ∃ w, g w = z ∧ 0 < g.residueDegree w := by
  obtain ⟨w₀, hw₀⟩ := hz
  let F := g.fiber z
  have hne : (Set.univ : Set F).Nonempty := ⟨(g.fiberHomeo z).symm ⟨w₀, hw₀⟩, trivial⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton isClosed_univ hne
  have h₁ : LocallyOfFiniteType (F.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h₂ : LocallyOfFiniteType (g.fiberToSpecResidueField z) := by
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let h : F ⟶ Z := g.fiberι z ≫ g
  have e : h x = z := by
    have := (g.range_fiberι z).le ⟨x, rfl⟩
    simpa [h] using this
  let β : Z.residueField z ⟶ F.residueField x := (Z.residueFieldCongr e.symm).hom ≫ h.residueFieldMap x
  have hβ : Spec.map β = F.fromSpecResidueField x ≫ g.fiberToSpecResidueField z := by
    rw [← cancel_mono (Z.fromSpecResidueField z)]
    simp only [β, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp [h, Scheme.Hom.fiber_fac]
  have hβft : β.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map β) := hβ ▸ inferInstance
    exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) |>.mp this
  have hβf : β.hom.Finite := by
    letI := β.hom.toAlgebra
    haveI : Algebra.FiniteType (Z.residueField z) (F.residueField x) := hβft
    exact finite_of_finite_type_of_isJacobsonRing _ _
  have hhf : (h.residueFieldMap x).hom.Finite := by
    have : h.residueFieldMap x = (Z.residueFieldCongr e.symm).inv ≫ β := by simp [β]
    rw [this, CommRingCat.hom_comp]
    exact hβf.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Z.residueFieldCongr e.symm).inv).2)
  refine ⟨g.fiberι z x, e, ?_⟩
  rw [show h.residueFieldMap x = g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x
    from Scheme.residueFieldMap_comp _ _ _] at hhf
  letI := (g.residueFieldMap (g.fiberι z x)).hom.toAlgebra
  letI := ((g.fiberι z).residueFieldMap x).hom.toAlgebra
  letI := (g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x))
      (F.residueField x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (F.residueField x) := hhf
  let φ := IsScalarTower.toAlgHom (Z.residueField (g (g.fiberι z x)))
    (W.residueField (g.fiberι z x)) (F.residueField x)
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x)) :=
    Module.Finite.of_injective φ.toLinearMap φ.toRingHom.injective
  exact Module.finrank_pos

end GlobalTheory

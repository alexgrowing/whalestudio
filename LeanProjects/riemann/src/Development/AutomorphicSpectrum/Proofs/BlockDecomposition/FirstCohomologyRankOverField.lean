import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open scoped CategoryTheory.Obj

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField

theorem vb_of_field (hFlat : FlatBCSt) (hLe : PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe) (hGe : H1DimGeAbelianDim) (k : Type) [Field k]
    (A : Over (Sp k)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hsm : SmoothOfRelativeDimension g A.hom) : VB k (HO1 A.hom) g := by
  let K := AlgebraicClosure k
  have hφ := isGrpPullback_pullback A (spMap (algebraMap k K))
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hφ
  have hsm' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap k K))).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hsm
  obtain ⟨hfin, hle⟩ := hLe k A g hab hsm
  obtain ⟨hfin', hle'⟩ := hLe K _ g hab' hsm'
  have hge := hGe K _ g hab' hsm' hfin'
  have := hab.proper
  obtain ⟨e, -⟩ := hFlat k K _ _ A.hom _ _ hφ.1 inferInstance inferInstance
  have hrank : Module.finrank k (HO1 A.hom) = g := by
    have h1 := e.finrank_eq
    rw [Module.finrank_baseChange] at h1
    omega
  refine ⟨hfin, inferInstance, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, hrank]
  rfl

theorem first_cohomology_rank_over_field : FlatBCSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe → H1DimGeAbelianDim → H1StructureFieldDim := by
  intro hFlat hLe hGe R _ A _ g hab hsm hR
  letI := hR.toField
  exact vb_of_field hFlat hLe hGe R A g hab hsm

end GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField

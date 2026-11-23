import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EtaleMulNAndIsOpenOmOfIsSemiAbelian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseChangeTestOfSurjectiveMulAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormsOfTestsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwoGoodSectionsNearClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFacOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalSectionNeZeroOnFibresStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem exists_extension_with_section : Semi.extend_existsSt.{0} → Out.MulNSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → C.HasTests → C.TorsSec n → T.Few n → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  intro hE hM hS C L T n hG hT hTors hFew
  have hB : T.BTest L := GlobalTheory.T.baseChangeTest_of_surjective_mul_abelianVariety hS C L T
  have hO : IsOpen (T.Om L) := (GlobalTheory.ZJ.etale_mulN_and_isOpen_om_of_isSemiAbelian C L T hG hM).2
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_norms_of_tests hE C L T hT hB
  have h6 : L.CompanionTheory (T.Om L) := GlobalTheory.T.companionTheory_om_of_tests_torsionSections hE C L T n hT hB hTors hFew
  have hγ := GlobalTheory.ZJ.Core.exists_gen_normOne C L T (T.Om L) ν hO hν h6
  obtain ⟨-, hlft, -, hint, hflat, -, hop, -⟩ := core_basic C
  have := C.lft
  have hsm : Smooth C.GG.hom := by
    have := L.smooth
    exact SmoothOfRelativeDimension.smooth C.g _
  have hN : Geo.Tor.IsNormalScheme C.G.toScheme := fun x =>
    GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth C.GG.hom C.normal x
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  exact GlobalTheory.T.exists_local_section_ne_zero_on_fibres' C L T (T.Om L) ν hO hν h6
    (@GlobalTheory.exists_lineBundle_of_normOne_generators C.G.toScheme C.A.left hint (C.GG.hom ≫ C.π) hflat hlft' hN C.a hop T.L.L T.L.isLB ν hν.isNrm hγ)

end GlobalTheory.ZJ

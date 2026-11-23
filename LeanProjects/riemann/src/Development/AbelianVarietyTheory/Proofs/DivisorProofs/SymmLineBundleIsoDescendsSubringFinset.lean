import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsFiniteType
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem symm_lbIso_descends_to_subring_containing_finset : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := by
  intro R _ S A _ _ B _ _ φ φ₂ P P₀ hB hφ sq hP hP₀ hw hsym
  haveI := hB.proper
  have hprop : IsProper (G2 B).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : QuasiCompact (G2 B).hom := inferInstance
  haveI : QuasiSeparated (G2 B).hom := inferInstance
  set sw₀ := (lift (snd B B) (fst B B)).left with hsw₀
  have hpb := isPullback_square hφ.1 φ₂ sq
  have H : LBIso (P₀.pull φ₂) ((P₀.pull sw₀).pull φ₂) :=
    LBIso.trans (pull_isLB hP₀ _) hP (pull_isLB (pull_isLB hP₀ _) _) hw.symm
      (LBIso.trans hP (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _) hsym
        (lbIso_square hP hP₀ hw (lift_square sq sq.2.symm sq.1.symm)))
  obtain ⟨F, hF⟩ := lbIso_descends_to_subring_containing_finset R S (G2 A).left (G2 B).left (G2 A).hom
    (G2 B).hom φ₂ P₀ (P₀.pull sw₀) hpb hP₀ (pull_isLB hP₀ _) H
  refine ⟨F, fun R₁ h hF₁ => ?_⟩
  have hpb₁ := isPullback_square (isGrpPullback (spMap (Subring.inclusion h)) B).1 _
    (isSquare (spMap (Subring.inclusion h)) B)
  have H₁ := hF R₁ h hF₁ _ _ _ hpb₁
  have e := lift_swap (spMap (Subring.inclusion h)) B
  refine LBIso.trans (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB (pull_isLB hP₀ _) _) H₁ ?_
  exact lbIso_square (pull_isLB hP₀ _) hP₀ (lbIso_refl (pull_isLB hP₀ sw₀)) e.symm

end GlobalTheory

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

namespace GlobalTheory

theorem lbIso_triv_pull_triv {X Y : Scheme.{0}} (f : Y ⟶ X) : LBIso ((LB.triv X).pull f) (LB.triv Y) :=
  Ex.ValInh.lbIso_of_g_one (fun i j => by
    simp only [LB.pull, LB.LinComb, LB.triv, map_one, one_zpow, Finset.prod_const_one]
    simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
    exact (res _).map_one) (fun i j => rfl)

theorem exists_finset_gen_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := by
  intro R _ S A _ _ B _ _ φ φ₂ P P₀ a a₀ hB hφ sq hP hP₀ hw e ht
  haveI := hB.proper
  have hN : (P₀.pull a₀.left).IsLB := pull_isLB hP₀ _
  have hT : ∀ X : Scheme.{0}, (LB.triv X).IsLB := fun X => LB.isLB_triv X
  have H₀ : LBIso (LB.triv A.left) ((P₀.pull a₀.left).pull φ) :=
    LBIso.trans (hT _) (pull_isLB hP _) (pull_isLB hN _) ((CechPic.iso_triv_iff _).2 ht)
      (lbIso_square hP hP₀ hw e)
  have H : LBIso ((LB.triv B.left).pull φ) ((P₀.pull a₀.left).pull φ) :=
    LBIso.trans (pull_isLB (hT _) _) (hT _) (pull_isLB hN _) (lbIso_triv_pull_triv φ) H₀
  obtain ⟨F, hF⟩ := lbIso_descends_to_subring_containing_finset R S A.left B.left A.hom B.hom φ
    (LB.triv B.left) (P₀.pull a₀.left) hφ.1 (hT _) hN H
  refine ⟨F, fun R₁ h hs a₁ e₁ => ?_⟩
  have H₁ := hF R₁ h hs _ _ (pφ (spMap (Subring.inclusion h)) B)
    (isGrpPullback (spMap (Subring.inclusion h)) B).1
  have H₂ : LBIso ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left)
      ((P₀.pull a₀.left).pull (pφ (spMap (Subring.inclusion h)) B)) :=
    lbIso_square (pull_isLB hP₀ _) hP₀ (PolBaseChange.lbIso_refl (pull_isLB hP₀ _)) e₁
  refine (CechPic.iso_triv_iff _).1 ?_
  exact LBIso.trans (hT _) (pull_isLB (hT _) _) (pull_isLB (pull_isLB hP₀ _) _)
    (lbIso_triv_pull_triv _).symm
    (LBIso.trans (pull_isLB (hT _) _) (pull_isLB hN _) (pull_isLB (pull_isLB hP₀ _) _) H₁ H₂.symm)

end GlobalTheory

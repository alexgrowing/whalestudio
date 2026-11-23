import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationPerfectPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfectPairOfGeometricFibresStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair := by
  intro H R _ A B _ _ g hA hB hgA hgB P hP φ hφ
  obtain ⟨Fr, -, BC⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  obtain ⟨fA, pA, -⟩ := Published.AbelianDeRham.Free.prim Fr hA hgA
  obtain ⟨fB, pB, -⟩ := Published.AbelianDeRham.Free.prim Fr hB hgB
  refine GlobalTheory.T.isPerfectPair_of_geometric_fibres R (primDR A) (primDR B) φ ?_
  intro Ω _ _ _
  have iA := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap (algebraMap R Ω))
  have iB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B (spMap (algebraMap R Ω))
  obtain ⟨h, h₁, h₂⟩ := AbDual.exists_prod_pullback iA iB
  have hP' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hP.isLB h
  have perf' := AbDual.IsPerfect.baseChange iA iB h₁ h₂ hP' (Cris.ChernExists.lbIso_refl hP') hP
  obtain ⟨φ', hφ', hcorr⟩ := hφ.pull hP.isLB (Published.AbelianDeRham.bcMor iA) (Published.AbelianDeRham.bcMor iB) h₁ h₂ hP'
    (Cris.ChernExists.lbIso_refl hP')
  have hA' := isAbelianScheme_pullback_obj (spMap (algebraMap R Ω)) A hA
  have hB' := isAbelianScheme_pullback_obj (spMap (algebraMap R Ω)) B hB
  have hgA' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R Ω))).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hgA
  have hgB' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R Ω))).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hgB
  exact ⟨primDR _, primDR _, inferInstance, inferInstance, inferInstance, inferInstance,
    (Published.AbelianDeRham.bcMor iA).pull, (Published.AbelianDeRham.bcMor iB).pull, φ',
    (BC R A g hA hgA Ω _ _ iA).1, (BC R B g hB hgB Ω _ _ iB).1,
    GlobalTheory.T.de_rham_polarization_perfect_pairing H Ω _ _ g hA' hB' hgA' hgB' _ perf' φ' hφ', fun x x' y y' hx hy ↦ hcorr x x' y y' hx hy⟩

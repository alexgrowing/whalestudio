import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraPeriodCoordinates
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIsoStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDiagonalCoordinatesOfDeterminantCondition
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_period_coordinates : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
    X.IsPullBy X₀ (spMap R.subtype) p →
    ∃ cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ v, ∃ v' : X.Lie, Obj.LieCorr R.subtype p v v' ∧ U.u.IsDiff (cd v) v'.hom) ∧
      (∀ v (v' : X.Lie) W, Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom → W = cd v) ∧
      ∀ ω : X₀.Lie →ₗ[R] R, ∃ lam : Fin (Module.finrank ℚ (FR E)) → ℂ, ∀ v, ((ω v : R) : ℂ) = ∑ j, lam j * cd v j := by
  first | exact @GlobalTheory.LieCoord.exists_lieCoord_unif | exact GlobalTheory.LieCoord.exists_lieCoord_unif | (intros; apply GlobalTheory.LieCoord.exists_lieCoord_unif <;> assumption)

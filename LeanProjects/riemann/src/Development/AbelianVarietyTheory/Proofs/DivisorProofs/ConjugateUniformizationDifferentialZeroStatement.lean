import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUniformizationDifferentialZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_uniformization_differential_zero : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (n n' : ℕ) (u : HolUnif A L n)
    (u' : HolUnif A' L' n') (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
    v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff 0 v → u'.IsDiff 0 v' := by
  first | exact @GlobalTheory.ConjTangent.isDiff_zero_of_isGrpPullback | exact GlobalTheory.ConjTangent.isDiff_zero_of_isGrpPullback | (intros; apply GlobalTheory.ConjTangent.isDiff_zero_of_isGrpPullback <;> assumption)

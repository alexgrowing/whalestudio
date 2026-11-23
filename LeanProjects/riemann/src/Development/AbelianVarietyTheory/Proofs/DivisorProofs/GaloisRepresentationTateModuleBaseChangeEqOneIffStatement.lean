import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepresentationTateModule_baseChange_eq_one_iff : ∀ (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] [IsCommMonObj ((Over.pullback (spMap (algebraMap K L))).obj A)] (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[L] Ω), galTate ((Over.pullback (spMap (algebraMap K L))).obj A) l σ = 1 ↔ galTate A l (σ.restrictScalars K) = 1 := by
  first | exact @GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff | exact GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff | (intros; apply GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff <;> assumption)

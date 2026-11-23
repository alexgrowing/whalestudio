import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionEulerProductConvergent
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_group_points_injective_mul : ∀ (G G' : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (g : ℂ ≃+* ℂ) (p : G'.left ⟶ G.left), IsGrpPullback G' G (spMap (g : ℂ →+* ℂ)) p → (∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q) ∧ (∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'), P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left → (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left) ∧ ∀ (J : Type) (s : Finset J) (P : J → (𝟙_ (Over (Sp ℂ)) ⟶ G)) (P' : J → (𝟙_ (Over (Sp ℂ)) ⟶ G')), (∀ i ∈ s, (P' i).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P i).left) → (∏ i ∈ s, P' i : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (∏ i ∈ s, P i : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
  first | exact @GlobalTheory.GrpPullback.points_conj | exact GlobalTheory.GrpPullback.points_conj | (intros; apply GlobalTheory.GrpPullback.points_conj <;> assumption)

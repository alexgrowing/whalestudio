import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealValDifferentEqOne
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
theorem _root_.GlobalTheory.T.elliptic_map_tangent_differential : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (n : ℕ) (u : HolUnif A L n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (f : scheme (curve Λ Ω) ⟶ A.left) (β₁ : Fin n → ℂ), (∀ z, pt Λ Ω z ≫ f = (u.ex (z • β₁)).left) → ∀ (c : ℂ) (v : epsR ℂ ⟶ A), v.left = tan (curve Λ Ω) c ≫ f → IsTangent v ∧ u.IsDiff ((c / Ω) • β₁) v := by
  first | exact @GlobalTheory.CMTorsionTangent.isTangent_and_isDiff | exact GlobalTheory.CMTorsionTangent.isTangent_and_isDiff | (intros; apply GlobalTheory.CMTorsionTangent.isTangent_and_isDiff <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistFunctionDecomposition
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
theorem _root_.GlobalTheory.T.conjugate_curve_point_addition_compat : ∀ (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (g : ℂ ≃+* ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 → ∀ h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁, (∀ z', ∃ z, pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z) ∧ ∀ z w z' w', pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z → pt Λ₁ Ω₁ w' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ w → pt Λ₁ Ω₁ (z' + w') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (z + w) := by
  first | exact @GlobalTheory.CMTorsion.Conj.pt_conj_onto_add | exact GlobalTheory.CMTorsion.Conj.pt_conj_onto_add | (intros; apply GlobalTheory.CMTorsion.Conj.pt_conj_onto_add <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticMapTangentDifferential
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
theorem _root_.GlobalTheory.T.elliptic_map_uniformization_line : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ f : scheme (curve Λ Ω) ⟶ X.A.left, f ≫ X.A.hom = toSpec (curve Λ Ω) → ∀ e : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ X.A), (∀ z w, e (z + w) = e z * e w) → (∀ z, (e z).left = pt Λ Ω z ≫ f) → ∃ β₁ : Fin n → ℂ, ∀ z, pt Λ Ω z ≫ f = (u.ex (z • β₁)).left := by
  first | exact @GlobalTheory.CMTorsion.exists_vector_of_additive_curve_hom | exact GlobalTheory.CMTorsion.exists_vector_of_additive_curve_hom | (intros; apply GlobalTheory.CMTorsion.exists_vector_of_additive_curve_hom <;> assumption)

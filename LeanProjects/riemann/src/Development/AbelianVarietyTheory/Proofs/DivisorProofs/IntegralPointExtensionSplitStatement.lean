import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_extension_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K] (ξ : Sp K ⟶ X) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) → SplitK t ξ q → ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K] (x : Sp R ⟶ X), spMap (algebraMap R K) ≫ x = ξ → Finite (TorsK t ξ q →* Kˣ) ∧ ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X), IsLocalHom ψ → spMap ψ ≫ x = z → (∀ χ : TorsK t ξ q →* Kˣ, ∃ c : TorsChar t z q, InducedBy χ x (algebraMap R K) ψ c) ∧ (∀ c : TorsChar t z q, ∃ χ : TorsK t ξ q →* Kˣ, InducedBy χ x (algebraMap R K) ψ c) ∧ ∀ (χ : TorsK t ξ q →* Kˣ) (c c' : TorsChar t z q), InducedBy χ x (algebraMap R K) ψ c → InducedBy χ x (algebraMap R K) ψ c' → Agree c c' := by
  first | exact @GlobalTheory.HtChar.induced_chars | exact GlobalTheory.HtChar.induced_chars | (intros; apply GlobalTheory.HtChar.induced_chars <;> assumption)

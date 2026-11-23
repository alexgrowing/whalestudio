import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointTorsionSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_torsion_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K] (ξ : Sp K ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ), SplitK t ξ (p ^ n) → ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra A K] [IsFractionRing A K] (x₀ : Sp A ⟶ X), spMap (algebraMap A K) ≫ x₀ = ξ → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), (∀ i, IsTanAtG t x₀ (e i)) → ∀ χ : TorsK t ξ (p ^ n) →* Kˣ, ∃ h : Fin g → A, ∀ (R : Type) [CommRing R] (φ : A →+* R) (u : R →+* K) (x : Sp R ⟶ X) (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X) (c : TorsChar t z (p ^ n)), u.comp φ = algebraMap A K → spMap φ ≫ x₀ = x → IsLocalHom ψ → spMap ψ ≫ x = z → InducedBy χ x u ψ c → DlogIs t p n c (fun i => spMap (dualMap (ψ.comp φ)) ≫ e i) (fun i => ψ (φ (h i))) := by
  first | exact @GlobalTheory.HtGen.dlog_regular_of_chart | exact GlobalTheory.HtGen.dlog_regular_of_chart | (intros; apply GlobalTheory.HtGen.dlog_regular_of_chart <;> assumption)

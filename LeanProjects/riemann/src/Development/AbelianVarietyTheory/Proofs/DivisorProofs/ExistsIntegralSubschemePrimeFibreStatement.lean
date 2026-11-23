import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSubschemePrimeFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_subscheme_prime_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (l : ℕ) [Fact l.Prime] (z : X), 0 < Scheme.ord ((l : X.functionField)) z → ∃ (Z : Scheme.{0}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (_ : Algebra (ZMod l) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = D := by
  first | exact @GlobalTheory.VertDivisor.exists_vertical_prime_divisor | exact GlobalTheory.VertDivisor.exists_vertical_prime_divisor | (intros; apply GlobalTheory.VertDivisor.exists_vertical_prime_divisor <;> assumption)

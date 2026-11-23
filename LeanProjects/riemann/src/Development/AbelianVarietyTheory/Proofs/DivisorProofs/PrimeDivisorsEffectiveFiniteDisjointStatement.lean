import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorsEffectiveFiniteDisjoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_divisors_effective_finite_disjoint : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ l : ℕ, l.Prime → (∀ z, 0 ≤ Scheme.ord ((l : X.functionField)) z) ∧ (Function.support fun z => Scheme.ord ((l : X.functionField)) z).Finite ∧ ∀ l' : ℕ, l'.Prime → l ≠ l' → ∀ z, Scheme.ord ((l : X.functionField)) z = 0 ∨ Scheme.ord ((l' : X.functionField)) z = 0 := by
  first | exact @GlobalTheory.PrimeOrd.prime_ord | exact GlobalTheory.PrimeOrd.prime_ord | (intros; apply GlobalTheory.PrimeOrd.prime_ord <;> assumption)

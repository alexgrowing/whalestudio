import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorIntegralSubschemeDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_divisor_integral_subscheme_dimension : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ num : Form (Cl p) D, IsArForm D num → ∀ (N : Fin D → HermLB p) (l : ℕ) [Fact l.Prime] (d : X → ℝ), (∀ z, Scheme.ord ((l : X.functionField)) z ≠ 0 → ∃ (Z : Scheme.{0}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (_ : Algebra (ZMod l) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = D ∧ d z = interNum (ZMod l) (structureModule Z) (fun j => (N j).B.pull i)) → ∑ᶠ z, (Scheme.ord ((l : X.functionField)) z : ℝ) * d z = num (Fin.cons (cl (oneB p)) fun j => cl (N j)) := by
  first | exact @GlobalTheory.VertFibre.finsum_ord_mul_deg_eq | exact GlobalTheory.VertFibre.finsum_ord_mul_deg_eq | (intros; apply GlobalTheory.VertFibre.finsum_ord_mul_deg_eq <;> assumption)

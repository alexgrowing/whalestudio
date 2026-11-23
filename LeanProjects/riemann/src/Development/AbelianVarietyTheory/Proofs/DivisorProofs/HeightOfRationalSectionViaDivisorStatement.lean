import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfRationalSectionViaDivisor
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_of_rational_section_via_divisor : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ num : Form (Cl p) D, IsArForm D num → ∀ (M : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (∀ σ, ∀ y ∈ offSupp p σ (M.div hr), logNorm (M.φ σ) r y = 0) → ∀ (N : Fin D → HermLB p) (ℓ : X → ℕ) (d : X → ℝ), (∀ z, (M.div hr).mult z ≠ 0 → ∃ (_ : Fact (ℓ z).Prime) (Z : Scheme.{0}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (_ : Algebra (ZMod (ℓ z)) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = D ∧ d z = interNum (ZMod (ℓ z)) (structureModule Z) (fun j => (N j).B.pull i)) → num (Fin.cons (cl M) fun j => cl (N j)) = ∑ᶠ z, ((M.div hr).mult z : ℝ) * d z * Real.log (ℓ z) := by
  first | exact @GlobalTheory.VertMix.vertMix | exact GlobalTheory.VertMix.vertMix | (intros; apply GlobalTheory.VertMix.vertMix <;> assumption)

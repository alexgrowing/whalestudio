import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterGermValuationEqColumnTyped
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characterGerm_valuation_eq_columnTyped : ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (B : FB O d OE) (h : PS C 2 d), B.IsCanonGauge C h → ∀ (w0 : OE) (k n : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) [Fintype (Letter Ty r n)] (σ : Ty → (OE →+* O)) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → O), (∀ ℓ a, (linPart (B.A.act a)).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ τ, ∃ a0, IsUnit (σ τ a0 - σ τ (star a0))) → (∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧ ∀ τ, ∃ a : OE, star a * a = (N : OE) ∧ v (algebraMap O C (σ τ a - 1)) < v (algebraMap O C x)) → ∀ (ty : Fin n → Ty) (P : MvPolynomial (Letter Ty r n) O), (∀ mo ∈ P.support, ∀ ℓ, mo ℓ ≠ 0 → ℓ.1 = ty ℓ.2.2) → ∀ χ : Fin n → PS O 1 d, (∀ b, IsCh B.G.F (χ b)) → MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P ≠ 0 → ∃ f : PS O n d, v (nabValN B C h w0 k (MvPowerSeries.map (algebraMap O C) f) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun (ℓ : Letter Ty r n) i => algebraMap O C (u ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap O C) P)) = v (algebraMap O C (MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P)) := by
  first | exact @GlobalTheory.CharValue.exists_germ_valuation_eq | exact GlobalTheory.CharValue.exists_germ_valuation_eq | (intros; apply GlobalTheory.CharValue.exists_germ_valuation_eq <;> assumption)

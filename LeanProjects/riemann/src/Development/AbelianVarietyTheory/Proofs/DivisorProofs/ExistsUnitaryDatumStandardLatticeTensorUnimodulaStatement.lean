import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDatumStandardLatticeTensorUnimodula
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_datum_standardLattice_tensor_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ g s : ℕ, r = s * Module.finrank ℚ E → ∃ (Dm : Datum H) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), Dm.p = s * g ∧ Dm.q = s * g ∧ (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) ∧ ∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1) := by
  first | exact @GlobalTheory.UnitaryStd.exists_datum | exact GlobalTheory.UnitaryStd.exists_datum | (intros; apply GlobalTheory.UnitaryStd.exists_datum <;> assumption)

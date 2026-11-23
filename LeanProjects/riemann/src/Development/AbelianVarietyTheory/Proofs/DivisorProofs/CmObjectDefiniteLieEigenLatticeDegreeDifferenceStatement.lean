import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmObjectDefiniteLieEigenLatticeDegreeDifference
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmObject_definite_lieEigenLattice_degree_difference : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (F : GlobalTheory.CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → q = 0 → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = ((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  first | exact @GlobalTheory.FlatCore.CMDiff0.cmDiff_definite | exact GlobalTheory.FlatCore.CMDiff0.cmDiff_definite | (intros; apply GlobalTheory.FlatCore.CMDiff0.cmDiff_definite <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (T : PAT H (Sp (𝓞 K))) (F : GenFib T.pol) (p q : ℕ), Splits E K → HasType H T.t.act ρ p q → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ τ : 𝓞 E →+* 𝓞 K, latRank K (F.eigLat T.t.act τ) = open Classical in if τ H.rt = ρ then p else q) ∧ iSupIndep (fun τ : 𝓞 E →+* 𝓞 K => Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K))) ∧ ⨆ τ : 𝓞 E →+* 𝓞 K, Submodule.span K (F.eigLat T.t.act τ : Set (Fin F.P₀.g → K)) = ⊤ ∧ T.g = Module.finrank ℚ E / 2 * (p + q) ∧ Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = ρ} = Module.finrank ℚ E / 2 ∧ Nat.card {τ : 𝓞 E →+* 𝓞 K // τ H.rt = -ρ} = Module.finrank ℚ E / 2 := by
  first | exact @GlobalTheory.CM.EigDec.eigen_decomposition | exact GlobalTheory.CM.EigDec.eigen_decomposition | (intros; apply GlobalTheory.CM.EigDec.eigen_decomposition <;> assumption)

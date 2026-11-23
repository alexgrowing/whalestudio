import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngehrnSiuCutLowerCentreDimension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.angehrnSiu_cut_lower_centre_dimension : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (r : ℕ) (N₀ : LB X) (hN₀ : N₀.IsLB) (A F : CartierDiv X) (a : ℕ)
      (x z : X) (e : ℕ) (c' : ℝ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → 0 < r → IsNef ℂ N₀ →
      IsAmpleLB (toLB A) → 0 < a → toPic F = a • cls N₀ hN₀ →
      IsClosed ({x} : Set X) → z ⤳ x → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e →
      (z = genericPoint X ∨ IsNkltCentre p n (Δ + qWeil D₀ m') z) → 0 < c' →
      c' ^ e < (interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e →
      0 < m' → D₀.Eff → 0 < μ → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) → LcAt p n (Δ + qWeil D₀ m') x →
      ∃ (lam' μ' : ℚ) (m'' : ℕ) (D₁ : CartierDiv X), 0 < m'' ∧ D₁.Eff ∧ 0 < μ' ∧ (lam' : ℝ) < lam + e / c' ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₁] : ℚ) / m'' = lam' * interNumRed ℂ C ![N₀] / r - μ' * interNumRed ℂ C ![toLB A]) ∧ LcCut p n (Δ + qWeil D₁ m'') x (e - 1) := by
  first | exact @GlobalTheory.PairStep.logCanonicalCut_lowers_centre_dimension | exact GlobalTheory.PairStep.logCanonicalCut_lowers_centre_dimension | (intros; apply GlobalTheory.PairStep.logCanonicalCut_lowers_centre_dimension <;> assumption)

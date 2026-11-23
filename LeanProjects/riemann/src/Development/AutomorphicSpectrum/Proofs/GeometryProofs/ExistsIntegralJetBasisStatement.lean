import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralJetBasis
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_jet_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (n r : ℕ) (s : Fin r → Out.H0 D.t.PP.L n), ∃ J : ℕ → Fin r → L, (∀ (i : ℕ) (c : Fin r → 𝓞 L), (∀ k < i, ∑ j, (c j : L) * J k j = 0) → IsIntegral ℤ (∑ j, (c j : L) * J i j)) ∧ ∀ (σ : L →+* ℂ) (a : D.Frame σ) (f : Fin r → (Fin D.g → ℂ) → ℂ) (v : Fin D.g → ℂ), (∀ j, a.IsFn (s j) (f j)) → D.IsVec a x v → ∀ (i : ℕ) (c : Fin r → ℂ), ((∀ k < i, ∑ j, c j * σ (J k j) = 0) ↔ ∀ k < i, iteratedDeriv k (fun τ : ℂ => ∑ j, c j * f j (τ • v)) 0 = 0) ∧ ((∀ k < i, ∑ j, c j * σ (J k j) = 0) → ∑ j, c j * σ (J i j) = iteratedDeriv i (fun τ : ℂ => ∑ j, c j * f j (τ • v)) 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.JetMain.jets | exact GlobalTheory.CompanionTheory.Ar.JetMain.jets | (intros; apply GlobalTheory.CompanionTheory.Ar.JetMain.jets <;> assumption)

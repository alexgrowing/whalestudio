import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecond
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact

theorem chart_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, (∀ τ, IsBlockDiag j (pH keep h ε τ w) ∧ (pH keep h ε τ w).det ≠ 0) ∧ pBase M v (pPhi M F keep v bl h ε w) = bl (pB ε w) ∧ ∀ p k, keep p → M.blk p = some k → ∀ m : ι k, upV v (pPhi M F keep v bl h ε w) ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (bl (pB ε w)) * minorIJ (pH keep h ε p.1 w) I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc w hw
  obtain ⟨hbm, hran, -, -, -, -, hh⟩ := hc
  have key : ∀ q : Σ k, ι k, q.1 ∈ Set.range κ → upV v (pPhi M F keep v bl h ε w) q =
      flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w) q := by
    intro q hq
    obtain ⟨q', rfl⟩ := hbm.2.2.2 q hq
    rw [upV_apply hbm.2.1]
    rfl
  refine ⟨fun τ => ⟨?_, ?_⟩, ?_, fun p k hk hp m => ?_⟩
  · exact isBlockDiag_mul (hh τ).1 (WMan.Exact.lowMat_isBlockDiag _ _)
  · rw [pH, Matrix.det_mul, pMat, WMan.Exact.lowMat_det, mul_one]
    exact (hh τ).2
  · funext q
    obtain ⟨k, m⟩ := q
    show upV v (pPhi M F keep v bl h ε w) ⟨k.1, m⟩ = _
    rw [key ⟨k.1, m⟩ ((hran k.1).2 (Or.inl k.2))]
    exact WMan.Exact.flagZ_base k m
  · rw [key ⟨k, m⟩ ((hran k).2 (Or.inr ⟨p, hk, hp⟩))]
    exact WMan.Exact.flagZ_step hp m

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact

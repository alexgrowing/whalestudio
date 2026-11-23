import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFirst
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo

open GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo

section Flag

variable {Ψ : Type} {N j n e : ℕ}

theorem analytic_pMat (keep : Ψ × Fin N → Prop) (s : Set (Fin e → ℂ)) (ε : Fin n ⊕ PIdx j keep ≃ Fin e)
    (τ : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => pMat keep (pL ε w) τ a b) s := by
  unfold pMat lowMat
  by_cases hc : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · simp only [hc, dite_true]
    by_cases hs : Sep keep (⟨(τ, a, b), hc⟩ : LowIdx Ψ N j)
    · simp only [cExt, hs, dite_true, pL]
      exact analytic_coord _
    · simp only [cExt, hs, dite_false]
      exact analyticOnNhd_const
  · simp only [hc, dite_false]
    exact analyticOnNhd_const

theorem analytic_pH (keep : Ψ × Fin N → Prop) (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (τ : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => pH keep h ε τ w a b) s := by
  unfold pH
  exact analytic_mul_entry (fun _ => h τ) _ (fun _ _ => analyticOnNhd_const)
    (analytic_pMat keep s ε τ) a b

theorem analytic_pB {Λ : Type} (ε : Fin n ⊕ Λ ≃ Fin e) (V : Set (Fin n → ℂ)) :
    AnalyticOnNhd ℂ (pB ε) (pD ε V) := by
  have : pB ε = ⇑(ContinuousLinearMap.pi (R := ℂ) fun i : Fin n =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (ε (Sum.inl i))) := by
    funext w i
    rfl
  rw [this]
  exact fun w _ => ContinuousLinearMap.analyticAt _ w

end Flag

theorem pPhi_holo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => pPhi M F keep v bl h ε w p) (pD ε V) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc p
  obtain ⟨-, -, -, hb, -⟩ := hc
  obtain ⟨-, -, hbl, hval, -⟩ := hb
  have hmap : Set.MapsTo (pB ε) (pD ε V) V := fun w hw => hw
  have hzb : ∀ q, AnalyticOnNhd ℂ (fun w => bl (pB ε w) q) (pD ε V) := fun q =>
    (hbl q).comp (analytic_pB ε V) hmap
  have hv : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl (pB ε w))) (pD ε V) := fun q I =>
    (hval q I).comp (analytic_pB ε V) hmap
  exact analytic_flagZ M F (fun w => bl (pB ε w)) (fun w τ' => pH keep h ε τ' w) hzb hv
    (fun τ' => analytic_pH keep _ h ε τ') (v p)

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo

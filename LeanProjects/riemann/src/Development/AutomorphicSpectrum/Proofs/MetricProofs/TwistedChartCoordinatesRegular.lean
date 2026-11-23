import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsSNC RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) ![1] ![diagSet k₀ RW] := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c x
  obtain ⟨⟨F, H, hW⟩, hVo, hxV, hVs, -, hu, hu0, hd, -⟩ := hL x
  have hsrc : ((ψ x).restrOpen (V x) hVo).source = V x := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.mpr hVs
  refine ⟨(ψ x).restrOpen (V x) hVo, pa_compat_restr RW.A (ψ x) hW.1 (V x) hVo, by rw [hsrc]; exact hxV, ?_,
    fun _ => some (i₀ x), ?_, ?_, u x, ?_, ?_, ?_⟩
  · rw [hsrc]; exact subset_rfl
  · intro k k' _ _ _
    exact Subsingleton.elim k k'
  · intro k
    obtain rfl : k = 0 := Subsingleton.elim k 0
    rw [hsrc]
    ext w
    constructor
    · rintro ⟨hw, hwV⟩
      exact ⟨hwV, i₀ x, rfl, (hd w hwV).2 hw⟩
    · rintro ⟨hwV, i, hi, hw⟩
      obtain rfl : i₀ x = i := Option.some.inj hi
      exact ⟨(hd w hwV).1 hw, hwV⟩
  · rw [hsrc]; exact hu
  · rw [hsrc]; exact hu0
  · rw [hsrc]
    intro w _
    simp [diagSec]

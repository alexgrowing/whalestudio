import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isNormFn_logNormSec_diagSec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ (b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsNormFn M τ a k₀ ca cb RW fun x => logNormSec (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) x + c := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL b hb hab hk hca hcb hW c
    x z₀ z₁ F h t h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hd : IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hno := GlobalTheory.T.flag_adjacent_twisted_resolution K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hd
  obtain ⟨-, -, hx, -, -, -, hu, hiff, hnorm⟩ := hL x
  have hψ : ψ x x (i₀ x) ≠ 0 := fun h0 => hno ((hiff x hx).1 h0)
  have hn := hnorm x hx hψ z₀ z₁ F h t hd
  have hne : ‖u x x * ψ x x (i₀ x)‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero (hu x hx) hψ)
  show Real.log (‖u x x * ψ x x (i₀ x)‖ *
    Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x x)) + c))) + c = _
  rw [Real.log_mul hne (Real.exp_ne_zero _), Real.log_exp, ← hn]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

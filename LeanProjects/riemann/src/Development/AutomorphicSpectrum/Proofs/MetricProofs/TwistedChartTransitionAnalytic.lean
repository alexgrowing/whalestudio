import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem locSec_norm_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x x' : RW.X) (ψ ψ' : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb kb' : Fin Rb.A.n) (σ σ' : Fin n ↪ Fin e) (i₀ i₀' : Fin e) (V V' : Set RW.X) (u u' : RW.X → ℂ), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u → IsLocSec M Rb τ a k₀ ca cb RW pr x' ψ' kb' σ' i₀' V' u' → ∀ w ∈ V ∩ V', ‖u w * ψ w i₀‖ / (potA M τ a k₀).h (RW.lift x w) = ‖u' w * ψ' w i₀'‖ / (potA M τ a k₀).h (RW.lift x' w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr x x' ψ ψ' kb kb' σ σ' i₀ i₀' V V' u u' _ _ hs hs' w hw
  obtain ⟨⟨F, H, hc⟩, -, -, hVs, hVU, -, hu, hd, hn⟩ := hs
  obtain ⟨-, -, -, -, hVU', -, hu', hd', hn'⟩ := hs'
  by_cases h0 : ψ w i₀ = 0
  · have h0' : ψ' w i₀' = 0 := (hd' w hw.2).2 ((hd w hw.1).1 h0)
    simp [h0, h0']
  have h0' : ψ' w i₀' ≠ 0 := fun h => h0 ((hd w hw.1).2 ((hd' w hw.2).1 h))
  obtain ⟨-, hF, -, -, -, hp⟩ := hc
  obtain ⟨hH, hG, z₀, z₁, hz₀, hz₁, hex⟩ := hp w (hVs hw.1)
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by
    obtain ⟨c, hc0, hzc⟩ := hz₀
    have e₀ : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k =>
        (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk (fstPt k₀ (RW.lift w w)) q := by
      rw [hzc]; rfl
    rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
      (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk (fstPt k₀ (RW.lift w w)))]
    exact hG
  have hD : IsPtData M τ a k₀ ca cb RW w z₀ z₁ F (H τ (ψ w)) (ψ w i₀) :=
    ⟨hF, hG', hz₀, hz₁, (hH τ).1, (hH τ).2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  have e₁ := hn w hw.1 h0 z₀ z₁ F _ _ hD
  have e₂ := hn' w hw.2 h0' z₀ z₁ F _ _ hD
  have hA : 0 < (potA M τ a k₀).h (RW.lift x w) := (potA M τ a k₀).pos _ (RW.mem x w (hVU hw.1)).1
  have hA' : 0 < (potA M τ a k₀).h (RW.lift x' w) := (potA M τ a k₀).pos _ (RW.mem x' w (hVU' hw.2)).1
  have hN : 0 < ‖u w * ψ w i₀‖ := norm_pos_iff.2 (mul_ne_zero (hu w hw.1) h0)
  have hN' : 0 < ‖u' w * ψ' w i₀'‖ := norm_pos_iff.2 (mul_ne_zero (hu' w hw.2) h0')
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (div_pos hN hA)) (Set.mem_Ioi.2 (div_pos hN' hA')) ?_
  rw [Real.log_div hN.ne' hA.ne', Real.log_div hN'.ne' hA'.ne', e₁, e₂]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

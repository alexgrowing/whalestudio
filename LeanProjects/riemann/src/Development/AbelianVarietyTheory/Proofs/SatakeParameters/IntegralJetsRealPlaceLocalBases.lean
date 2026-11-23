import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.GaussJetBounds.StatementN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeJetsIntegralIffIntegralFrames
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralEigenCombination
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixUnitIntegralCombEmbeddedHomsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.integral_jets_realPlace_local_bases

theorem tauEmb_ringHom (D : D7) {p : ℕ} [Fact p.Prime] (lm : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ∃ g : D.host.E →+* ℂ_[p], ∀ x, tauEmb D lm τ x = g x := by
  have hm : ∀ x, embT D τ x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)
  exact ⟨lm.comp ((embT D τ).codRestrict Qbar hm), fun x => dif_pos (hm x)⟩

theorem jetsIntegral_basR : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  intro D cD hD N N' L L' hA p _ lm B B' κ hB hB' hκ F hF
  refine (GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames D N N' p lm (YYl D L L') F).2 hF _ _ ?_
  rintro ⟨j1, a, b⟩
  by_cases h0 : lamC lm (cD (tauPl D j1)) = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun ⟨τ, k1, k2⟩ => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    split_ifs with h
    · subst h
      have : κ (tauPl D j1) = 0 := by
        have := hκ (tauPl D j1); rw [h0, norm_zero] at this; exact norm_le_zero_iff.1 this
      simp [this]
    · rfl
  · set τ0 := tauPl D j1 with hτ0
    set c := κ τ0 / lamC lm (cD τ0) with hc
    have hcn : ‖c‖ ≤ 1 := by
      rw [hc, norm_div]; exact div_le_one_of_le₀ (hκ τ0) (norm_nonneg _)
    obtain ⟨n, r, aa, hr, haa, hsum⟩ := GlobalTheory.Proof.IntegralEigenCombination.eigGen_integral_comb D cD hD p lm τ0
    obtain ⟨m, r', A, hr', hA', hAsum⟩ :=
      GlobalTheory.T.matrixUnit_integral_comb_embedded_homs D N N' L L' hA p lm τ0 (B τ0) (B' τ0) (hB τ0) (hB' τ0) a b
    refine ⟨n * m, fun t => c * r (finProdFinEquiv.symm t).1 * r' (finProdFinEquiv.symm t).2,
      fun t => aa (finProdFinEquiv.symm t).1 • A (finProdFinEquiv.symm t).2, ?_, ?_, ?_⟩
    · intro t
      rw [norm_mul, norm_mul]
      calc ‖c‖ * ‖r _‖ * ‖r' _‖ ≤ 1 * 1 * 1 := by
            gcongr
            · exact hr _
            · exact hr' _
        _ = 1 := by norm_num
    · intro t
      exact Submodule.subset_span ⟨aa _, haa _, A _, hA' _, rfl⟩
    · rintro ⟨τ, k1, k2⟩
      obtain ⟨g, hg⟩ := tauEmb_ringHom D lm τ
      rw [← finProdFinEquiv.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type]
      have key : ∑ i : Fin n, ∑ j : Fin m, c * r i * r' j * tauEmb D lm τ ((aa i • A j) k1 k2)
          = c * ((∑ i, r i * tauEmb D lm τ (aa i)) * (∑ j, r' j * tauEmb D lm τ (A j k1 k2))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hg, Matrix.smul_apply, smul_eq_mul, map_mul]
        ring
      rw [key, hsum τ]
      split_ifs with h1 h2 h2
      · subst h2
        rw [← hAsum k1 k2, hc, ← mul_assoc, div_mul_cancel₀ _ h0, mul_assoc]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
end GlobalTheory.Proof.integral_jets_realPlace_local_bases

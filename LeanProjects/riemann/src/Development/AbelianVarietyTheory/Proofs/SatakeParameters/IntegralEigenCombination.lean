import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.GaussJetBounds.StatementN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.IntegralEigenCombination

theorem eigGen_integral_comb : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ τ : D.what₂.Tau, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (a : Fin n → D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, a j ∈ D.host.AA0) ∧ ∀ τ', ∑ j, r j * tauEmb D lm τ' (a j) = if τ' = τ then lamC lm (cD τ) else 0 := by
  intro D cD hD p _ lm τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hmem : s ∈ TaylorLogMetric.ellT D M τ := by rw [hsp]; exact Submodule.mem_span_singleton_self s
  have hv : (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s ∈ TaylorLogMetric.mmM D M :=
    Submodule.mem_comap.1 hmem
  obtain ⟨n, f, v, hfv⟩ := Submodule.mem_span_set'.1 hv
  have hva : ∀ j, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      (v j : D.what₂.Tau → M) = fun τ => TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ a) := fun j => (v j).2
  choose a ha hav using hva
  obtain ⟨g, hg⟩ := GlobalTheory.Proof.DirectionalDerivative.exists_lamHom lm (algebraMap M ℂ)
  have hg' : ∀ x : M, lamC lm (x : ℂ) = g x := hg
  refine ⟨n, fun j => g ((f j : 𝓞 M) : M), a, fun j => ?_, ha, fun τ' => ?_⟩
  · exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int g (f j).isIntegral_coe)
  · have e : ∀ j, tauEmb D lm τ' (a j) = g (TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) := by
      intro j
      rw [← hg', TaylorLogMetric.liftM, dif_pos (hM _ _)]
      rfl
    have hc := congrFun hfv τ'
    simp only [Finset.sum_apply, Pi.smul_apply, hav] at hc
    simp only [e, ← map_mul]
    rw [← map_sum]
    have hc' : (∑ j, ((f j : 𝓞 M) : M) * TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) =
        (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s τ' := by
      rw [← hc]; rfl
    rw [hc']
    by_cases h : τ' = τ
    · subst h; simp [hsc.symm, hg']
    · simp [h]
end GlobalTheory.Proof.IntegralEigenCombination

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

set_option maxHeartbeats 1000000 in

theorem base_term_norm_coords : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∀ g : GA D V, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ = ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ G Φ hG hΦ 𝓐 𝓑 hlay g
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  have hTL := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS
  have hsplit : ∀ (n : GA D V) (h : GA D W), om (n * g, h) Φ = om (n, 1) (om (g, h) Φ) := by
    intro n h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hψn : ∀ x, ‖ψ x‖ₑ = 1 := fun x => by
    rw [← ofReal_norm_eq_enorm, hω.std.1.2.1 x, ENNReal.ofReal_one]
  have hFm : Measurable (fun p : flagN d × GA D W =>
      ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ) := by
    refine Continuous.measurable ?_
    refine ((hG.2.1.comp continuous_snd).mul ?_).enorm
    exact ((hTL Φ hΦ).2.2.2.1 x₀).comp
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hfib : ∀ h : GA D W, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
      ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν =
      ∫⁻ n in 𝓐, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) x₀‖ₑ ∂vN.ν := by
    intro h
    have hΨ : IsThetaFunO ψ V W (om (g, h) Φ) := hω.om_pres (g, h) Φ hΦ
    have hfm : Measurable (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) :=
      (((hTL _ hΨ).2.2.2.1 x₀).comp (continuous_id.prodMk continuous_const)).enorm.measurable
    have hinv : ∀ c, ∀ n ∈ flagN d,
        (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) (d.nC c * n) =
        (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) n := by
      intro c n hn
      have hΨ' := hω.om_pres (n, 1) _ hΨ
      have t1 := (hTL _ hΨ').1 x₀ 0 1 c
      rw [d.nB_zero, OneMemClass.coe_one, map_one, mul_one, mul_one, ← Module.End.mul_apply, ← map_mul,
        Prod.mk_mul_mk, one_mul] at t1
      show ‖term ψ d W vS (om (d.nC c * n, 1) (om (g, h) Φ)) x₀‖ₑ =
        ‖term ψ d W vS (om (n, 1) (om (g, h) Φ)) x₀‖ₑ
      rw [t1, enorm_mul, hψn, one_mul]
      simp [term]
    have hval : ∀ (u : UX D ρ) (b : Mx D ρ V₀.rank),
        ‖term ψ d W vS (om (d.nB b * d.levi u.1, 1) (om (g, h) Φ)) x₀‖ₑ =
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ := by
      intro u b
      have t1 := (hTL _ hΨ).1 x₀ b u 0
      rw [d.nC_zero, one_mul] at t1
      rw [t1, enorm_mul, hψn, one_mul]
    have hl := hlay _ hfm hinv
    calc ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
          ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν
        = ‖G h‖ₑ * ∫⁻ n in 𝓐, ‖term ψ d W vS (om (n.1, 1) (om (g, h) Φ)) x₀‖ₑ ∂vN.ν := by
          rw [hl]
          simp only [hval]
      _ = ∫⁻ n in 𝓐, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) x₀‖ₑ ∂vN.ν := by
          rw [← lintegral_const_mul' _ _ enorm_ne_top]
          refine lintegral_congr fun n => ?_
          rw [enorm_mul, hsplit]
  rw [← Measure.prod_restrict, lintegral_prod_symm _ hFm.aemeasurable]
  refine lintegral_congr fun h => ?_
  exact hfib h

end GlobalTheory.Unf

end

import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.transl_small :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ), Integrable f μ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ b in 𝓝 (1 : G), ∫ g, ‖f (b * g) - f g‖ ∂μ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ μ _ f hf ε hε
  haveI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  have hm : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  set F : Lp ℂ 1 μ := hm.toLp f with hF
  have hc : Continuous fun b : G => ‖(DomMulAct.mk b) • F - F‖ :=
    ((DomMulAct.continuous_mk.smul continuous_const).sub continuous_const).norm
  have h1 : ‖(DomMulAct.mk (1 : G)) • F - F‖ < ε := by
    have : (DomMulAct.mk (1 : G)) • F = F := one_smul Gᵈᵐᵃ F
    rw [this, sub_self, norm_zero]; exact hε
  have hev := hc.continuousAt.eventually_lt continuousAt_const h1
  filter_upwards [hev] with b hb
  refine le_of_eq_of_le ?_ hb.le
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  have hFf : F =ᵐ[μ] f := hm.coeFn_toLp
  have h2 : (fun g => F (b * g)) =ᵐ[μ] fun g => f (b * g) :=
    (measurePreserving_mul_left μ b).quasiMeasurePreserving.ae_eq_comp hFf
  filter_upwards [Lp.coeFn_sub ((DomMulAct.mk b) • F) F, DomMulAct.smul_Lp_ae_eq (DomMulAct.mk b) F, hFf, h2] with g e1 e2 e3 e4
  rw [e1, Pi.sub_apply, e2, e3, ← e4]
  rfl

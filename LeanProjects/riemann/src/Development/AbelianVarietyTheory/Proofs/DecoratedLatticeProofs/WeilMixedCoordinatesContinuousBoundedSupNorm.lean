import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.MixCont

variable {D : D7}

theorem continuous_covolOne_integral {P : Type} [TopologicalSpace P] {m n : ℕ} {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓕) (F : P → Mx D m n → ℂ) (hF : Continuous (Function.uncurry F))
    (hper : ∀ p, ∀ γ ∈ ratMx D m n, ∀ a, F p (γ + a) = F p a) : Continuous fun p => ∫ a in 𝓕, F p a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hc : ∀ p, Continuous (F p) := fun p => hF.comp (continuous_const.prodMk continuous_id)
  rw [continuous_iff_continuousAt]
  intro p₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v, hv, hvK⟩ := hK.mem_uniformity_of_prod (s := Set.univ) (q := p₀) hF.continuousOn (Set.mem_univ _)
    (Metric.dist_mem_uniformity (half_pos hε))
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with p hp
  have hb : ∀ a ∈ 𝓕, ‖F p a - F p₀ a‖ ≤ ε / 2 := by
    intro a _
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hper p γ hγ a, ← hper p₀ γ hγ a, ← dist_eq_norm]
    exact (hvK p hp _ ha).le
  rw [dist_eq_norm, ← integral_sub (covolOne_integrableOn h _ (hc p) (hper p))
    (covolOne_integrableOn h _ (hc p₀) (hper p₀))]
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := 𝓕) (by rw [h.2.2]; exact ENNReal.one_lt_top) hb
  refine lt_of_le_of_lt h1 ?_
  simp [Measure.real, h.2.2]
  linarith

theorem integrandT_periodic_of_quasi {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ)
    {f : WO S T → ℂ} (hq : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) (y : Mx D S.rank σ)
    (w₀ : WO S T₀) (γ : Mx D σ S.rank) (hγ : γ ∈ ratMx D σ S.rank) (ξ : Mx D σ S.rank) :
    heisO ψ S T (d.incX S (γ + ξ)) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 =
      heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 := by
  obtain ⟨δ, hδ⟩ : d.incX S γ ∈ ratMx D _ _ := ratMx_mul (rat_mem _) hγ
  have h := hq δ (d.incX S ξ + d.incAdj S y + d.inc0 S w₀)
  rw [show ratW T S δ = d.incX S γ from hδ] at h
  rw [HypDec.integrandT_eq, HypDec.integrandT_eq, map_add (d.incX S), add_assoc (d.incX S γ), add_assoc (d.incX S γ), h,
    ← mul_assoc, ← AddChar.map_add_eq_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
    HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, zero_add, add_zero]
  rw [add_comm (symplOH S T (d.incX S γ) _), add_neg_cancel_right]

theorem mixed_coords_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle)
    (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ Φ, IsThetaFunO ψ V W Φ →
    (Continuous fun q : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W =>
      dV.mixS W ψ vS.μ vS.𝓕 (om q.1 Φ) q.2.1 q.2.2) ∧
    (Continuous fun q : (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀ =>
      evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (om q.1 Φ) q.2.1 q.2.2.1 q.2.2.2) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hw Φ hΦ
  have hψ : Continuous ψ := hw.std.1.1
  have hJ : Continuous fun p : (GA D V × GA D W) × WO V W => om p.1 Φ p.2 := GlobalTheory.Unf.jointCont_all D ψ V W χV χW om hw Φ hΦ
  have hth : ∀ p, IsThetaFunO ψ V W (om p Φ) := fun p => hw.om_pres p Φ hΦ
  have cX : Continuous (dV.extX W) := continuous_id.matrix_mul continuous_const
  have cY : Continuous (dV.extY W) := continuous_id.matrix_mul continuous_const
  have c0 : Continuous (dV.ext0 W) := continuous_id.matrix_mul continuous_const
  have h1 : Continuous fun q : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W =>
      dV.mixS W ψ vS.μ vS.𝓕 (om q.1 Φ) q.2.1 q.2.2 := by
    refine continuous_covolOne_integral vS.covol
      (fun (q : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) a => heisO ψ V W (dV.extY W a)
        (heisO ψ V W (dV.extX W q.2.1) (heisO ψ V W (dV.ext0 W q.2.2) (om q.1 Φ))) 0) ?_ ?_
    · have e : Function.uncurry (fun (q : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) a => heisO ψ V W (dV.extY W a)
          (heisO ψ V W (dV.extX W q.2.1) (heisO ψ V W (dV.ext0 W q.2.2) (om q.1 Φ))) 0) =
          fun z => ψ (symplOH V W (dV.extY W z.2) (dV.extX W z.1.2.1)) *
            om z.1.1 Φ (dV.extY W z.2 + dV.extX W z.1.2.1 + dV.ext0 W z.1.2.2) := by
        funext z; exact dV.integrandS_eq _ _ _ _
      rw [e]
      refine (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH (cY.comp continuous_snd)
        (cX.comp (continuous_fst.snd.fst)))).mul ?_
      exact hJ.comp (continuous_fst.fst.prodMk (((cY.comp continuous_snd).add (cX.comp continuous_fst.snd.fst)).add
        (c0.comp continuous_fst.snd.snd)))
    · intro q γ hγ a
      exact dV.integrandS_periodic (hth q.1) q.2.1 q.2.2 γ hγ a
  refine ⟨h1, ?_⟩
  have cXT : Continuous (dW.incX V₀) := continuous_const.matrix_mul continuous_id
  have cA : Continuous (dW.incAdj V₀) := by
    have e : (dW.incAdj V₀ : Mx D V₀.rank σ → WO V₀ W) =
        fun y : Mx D V₀.rank σ => dW.jY ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA V₀)) := by
      funext y; rfl
    rw [e]
    have h3 : Continuous fun y : Mx D V₀.rank σ => adj y ⬝ gA V₀ := continuous_adj.matrix_mul continuous_const
    have h4 : Continuous fun y : Mx D V₀.rank σ => incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA V₀) :=
      h3.const_smul (incA D (-D.host.xi0⁻¹))
    exact continuous_const.matrix_mul h4
  have cI : Continuous (dW.inc0 V₀) := continuous_const.matrix_mul continuous_id
  let G : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W → ℂ := fun q => dV.mixS W ψ vS.μ vS.𝓕 (om q.1 Φ) q.2.1 q.2.2
  have h2 : Continuous fun (q : (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) =>
      ∫ ξ in vT.𝓕, ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ q.2.2.1)) *
        G (q.1, q.2.1, dW.incX V₀ ξ + dW.incAdj V₀ q.2.2.1 + dW.inc0 V₀ q.2.2.2) ∂vT.μ := by
    refine continuous_covolOne_integral vT.covol
      (fun (q : (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) ξ =>
        ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ q.2.2.1)) *
        G (q.1, q.2.1, dW.incX V₀ ξ + dW.incAdj V₀ q.2.2.1 + dW.inc0 V₀ q.2.2.2)) ?_ ?_
    · refine (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH (cXT.comp continuous_snd)
        (cA.comp continuous_fst.snd.snd.fst))).mul ?_
      exact h1.comp (continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk
        (((cXT.comp continuous_snd).add (cA.comp continuous_fst.snd.snd.fst)).add (cI.comp continuous_fst.snd.snd.snd))))
    · intro q γ hγ ξ
      have := integrandT_periodic_of_quasi dW
        (fun δ w => GlobalTheory.MixModel.Check.mixS_quasi dV vS.μ vS.𝓕 (hth q.1) q.2.1 δ w) q.2.2.1 q.2.2.2 γ hγ ξ
      rw [HypDec.integrandT_eq, HypDec.integrandT_eq] at this
      exact this
  refine h2.congr fun q => ?_
  simp only [evalAt, HypDec.mixT, HypDec.integrandT_eq, G]

end GlobalTheory.MixCont

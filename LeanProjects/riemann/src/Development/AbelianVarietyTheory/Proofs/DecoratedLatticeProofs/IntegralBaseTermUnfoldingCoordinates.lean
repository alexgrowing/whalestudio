import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerIntegralToIntegralCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasures
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

set_option maxHeartbeats 1000000 in

theorem integral_base_term_coords : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), NullMeasurableSet 𝓐 vN.ν → NullMeasurableSet 𝓑 vW.μ → (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) ≠ ⊤ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ p in 𝓐 ×ˢ 𝓑, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ ∂(vN.ν.prod vW.μ) = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hTh G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑 hlay hfin
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank vb vU
  haveI : IsFiniteMeasure (vb.μ.restrict vb.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vb.covol.2.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  have hTL := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS
  have hsplit : ∀ (g : GA D V) (h : GA D W), om (g, h) Φ = om (g, 1) (om (1, h) Φ) := by
    intro g h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hψ1 : ∀ x, star (ψ x) * ψ x = 1 := fun x => by
    rw [Complex.star_def, Complex.conj_mul', hω.std.1.2.1 x]; norm_num
  have hq0 : d.qS W 0 (rat x₀) = 0 := by
    simp [HypDec.qS, symplOH, symplO, hO]
  set F : flagN d × GA D W → ℂ := fun p => Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ with hFdef
  have hFm : Measurable F := by
    refine Continuous.measurable ?_
    refine ((hTh.cont.comp continuous_fst).mul (hG.2.1.comp continuous_snd)).mul ?_
    exact ((hTL Φ hΦ).2.2.2.1 x₀).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hint : Integrable F ((vN.ν.restrict 𝓐).prod (vW.μ.restrict 𝓑)) := by
    rw [Measure.prod_restrict]
    exact ⟨hFm.aestronglyMeasurable, lt_top_iff_ne_top.2 hfin⟩
  have hpm : Measurable (Function.uncurry fun (u : UX D ρ) (b : Mx D ρ V₀.rank) => d.nB b * d.levi u.1) :=
    (d.continuous_nB.measurable.comp measurable_snd).mul
      ((d.continuous_levi.comp continuous_subtype_val).measurable.comp measurable_fst)
  have hfib : ∀ h, Integrable (fun n => F (n, h)) (vN.ν.restrict 𝓐) →
      ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐) = G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := by
    intro h hih
    classical
    have hΨ := hω.om_pres (1, h) Φ hΦ
    set f : GA D V → ℂ := (flagN d : Set (GA D V)).piecewise
      (fun g => Th g * G h * term ψ d W vS (om (g, h) Φ) x₀) 0 with hfdef
    have hfm : Measurable f := by
      refine ContinuousOn.measurable_piecewise ?_ continuousOn_const (GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)).measurableSet
      refine ((continuousOn_iff_continuous_restrict.2 hTh.cont).mul continuousOn_const).mul ?_
      exact (((hTL Φ hΦ).2.2.2.1 x₀).comp (continuous_id.prodMk continuous_const)).continuousOn
    have hfF : ∀ n : flagN d, f n.1 = F (n, h) := fun n => Set.piecewise_eq_of_mem _ _ _ n.2
    have hcen : ∀ (c : skewA D ρ) (n : GA D V), n ∈ flagN d →
        term ψ d W vS (om (d.nC c * n, h) Φ) x₀ = ψ (d.qS W c (rat x₀)) * term ψ d W vS (om (n, h) Φ) x₀ := by
      intro c n hn
      have hΨ' := hω.om_pres (n, h) Φ hΦ
      have t1 := (hTL _ hΨ').1 x₀ 0 1 c
      rw [d.nB_zero, OneMemClass.coe_one, map_one, mul_one, mul_one, ← Module.End.mul_apply, ← map_mul,
        Prod.mk_mul_mk, one_mul] at t1
      rw [t1]
      simp [term]
    have hfinv : ∀ t, (fun t : GA D V → GA D V => ∃ c, t = (d.nC c * ·)) t → ∀ n ∈ (flagN d : Set (GA D V)),
        f (t n) = f n := by
      rintro t ⟨c, rfl⟩ n hn
      have hm : d.nC c * n ∈ (flagN d : Set (GA D V)) := mul_mem (d.nC_mem_NFlag c) hn
      rw [hfdef, Set.piecewise_eq_of_mem _ _ _ hm, Set.piecewise_eq_of_mem _ _ _ hn, hTh.cen c n hn, hcen c n hn]
      calc star (ψ (d.qS W c (rat x₀))) * Th n * G h * (ψ (d.qS W c (rat x₀)) * term ψ d W vS (om (n, h) Φ) x₀)
          = (star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x₀))) * (Th n * G h * term ψ d W vS (om (n, h) Φ) x₀) := by
            ring
        _ = _ := by rw [hψ1, one_mul]
    have hcoord : ∀ (u : UX D ρ) (b : Mx D ρ V₀.rank),
        f (d.nB b * d.levi u.1) = G h * flFun ψ d W vS Th (rat x₀) (om (1, h) Φ) u b := by
      intro u b
      have hm : d.nB b * d.levi u.1 ∈ (flagN d : Set (GA D V)) := mul_mem (d.nB_mem_NFlag b) (d.levi_mem_NFlag u.2)
      have t1 := (hTL _ hΨ).1 x₀ b u 0
      rw [d.nC_zero, one_mul, hq0, AddChar.map_zero_eq_one, one_mul] at t1
      rw [hfdef, Set.piecewise_eq_of_mem _ _ _ hm, hsplit, t1, flFun]
      ring
    have hlay' : ∀ g : GA D V → ENNReal, Measurable g →
        (∀ t, (fun t : GA D V → GA D V => ∃ c, t = (d.nC c * ·)) t → ∀ n ∈ (flagN d : Set (GA D V)), g (t n) = g n) →
        ∫⁻ x, g (Subtype.val x) ∂(vN.ν.restrict 𝓐) =
          ∫⁻ u, ∫⁻ y, g ((fun (u : UX D ρ) (b : Mx D ρ V₀.rank) => d.nB b * d.levi u.1) u y) ∂(vb.μ.restrict vb.𝓕) ∂vU.ν :=
      fun g hg hinv => hlay g hg fun c n hn => hinv _ ⟨c, rfl⟩ n hn
    have hih' : Integrable (fun x : flagN d => f x.1) (vN.ν.restrict 𝓐) := by
      refine hih.congr (ae_of_all _ fun n => (hfF n).symm)
    obtain ⟨-, heq⟩ := GlobalTheory.T.lowerIntegral_to_integral_coordinates (flagN d) (UX D ρ) (Mx D ρ V₀.rank) (GA D V) (vN.ν.restrict 𝓐) vU.ν
      (vb.μ.restrict vb.𝓕) Subtype.val (fun u b => d.nB b * d.levi u.1) (fun t => ∃ c, t = (d.nC c * ·))
      measurable_subtype_coe hpm (flagN d) hlay' f hfm hfinv hih'
    calc ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐) = ∫ x, f x.1 ∂(vN.ν.restrict 𝓐) :=
          integral_congr_ae (ae_of_all _ fun n => (hfF n).symm)
      _ = ∫ u, ∫ b, f (d.nB b * d.levi u.1) ∂(vb.μ.restrict vb.𝓕) ∂vU.ν := heq
      _ = ∫ u, ∫ b, G h * flFun ψ d W vS Th (rat x₀) (om (1, h) Φ) u b ∂(vb.μ.restrict vb.𝓕) ∂vU.ν := by
          refine integral_congr_ae (ae_of_all _ fun u => ?_)
          exact integral_congr_ae (ae_of_all _ fun b => hcoord u b)
      _ = G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := by
          simp only [integral_const_mul]; rfl
  have hae := hint.prod_left_ae
  have hI := hint.integral_prod_right
  have hEq : (fun h => ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐)) =ᵐ[vW.μ.restrict 𝓑]
      fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := hae.mono fun h hh => hfib h hh
  refine ⟨hI.congr hEq, ?_⟩
  rw [← Measure.prod_restrict, integral_prod_symm F hint]
  exact integral_congr_ae hEq

end GlobalTheory.Unf

end

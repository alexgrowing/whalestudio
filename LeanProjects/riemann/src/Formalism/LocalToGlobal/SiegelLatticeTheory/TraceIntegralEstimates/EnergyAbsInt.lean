import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsBasic
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsRep

noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def φinv (p : G × G) : G := p.2⁻¹ * p.1

theorem continuous_φinv : Continuous (φinv : G × G → G) := by
  unfold φinv
  exact continuous_snd.inv.mul continuous_fst

theorem measurable_φinv : Measurable (φinv : G × G → G) := continuous_φinv.measurable

theorem coef_shift {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) (γ z u z' u' : G) :
    ⟪σ (u⁻¹ * z) w, σ γ (σ (u'⁻¹ * z') w)⟫_ℂ = ⟪σ z w, σ (u * γ * u'⁻¹) (σ z' w)⟫_ℂ := by
  obtain ⟨h1, hmul, hinn, -⟩ := hσ
  have e : ∀ a : HH, σ u (σ u⁻¹ a) = a := fun a => by
    rw [← ContinuousLinearMap.mul_apply, ← hmul, mul_inv_cancel, h1, ContinuousLinearMap.one_apply]
  rw [← hinn u, hmul u⁻¹ z, ContinuousLinearMap.mul_apply, e]
  simp only [hmul, ContinuousLinearMap.mul_apply]

theorem norm_W_shift {σ : G → (HH →L[ℂ] HH)} {μ ν : Measure G} {d : ℝ} {w : HH} {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V} (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S)
    {u : G} (hu : u ∈ S) (z : G) : ‖W (u⁻¹ * z)‖ = ‖W z‖ := by
  have hu' : u⁻¹ ∈ S := hinv u hu
  have h := hW.2.2.1 u⁻¹ hu' (W z) (W z)
  rw [hW.2.2.2.1 u⁻¹ hu' z, norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), h]

theorem enorm_rk1A_le (a : V) (b : V') : ‖rk1A a b‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  have h := norm_rk1A_le a b
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  push_cast
  exact h

def bInt (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (W' : G → V') (γ z z' s s' : G) : ℝ≥0∞ :=
  ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ

theorem continuous_coef5 {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) (γ : G) :
    Continuous (fun q : G × G × G × G => ⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹) (σ q.2.1 w)⟫_ℂ) := by
  obtain ⟨-, hmul, -, hc⟩ := hσ
  have e : (fun q : G × G × G × G => ⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹) (σ q.2.1 w)⟫_ℂ) =
      fun q => ⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹ * q.2.1) w⟫_ℂ := by
    funext q
    rw [hmul (q.2.2.1 * γ * q.2.2.2⁻¹) q.2.1, ContinuousLinearMap.mul_apply]
  rw [e]
  have hg : Continuous fun q : G × G × G × G => q.2.2.1 * γ * q.2.2.2⁻¹ * q.2.1 := by fun_prop
  exact ((hc w).comp continuous_fst).inner ((hc w).comp hg)

theorem lintegral_four {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    (f : G → G → G → G → ℝ≥0∞) (hf : Measurable (fun q : G × G × G × G => f q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    ∫⁻ p, f p.1.1 p.2.1 p.1.2 p.2.2 ∂((ν.prod μS).prod (ν'.prod μS')) =
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', f z z' s s' ∂μS' ∂μS ∂ν' ∂ν := by
  have hm : Measurable (fun p : (G × G) × (G × G) => f p.1.1 p.2.1 p.1.2 p.2.2) := by
    have hg : Measurable (fun p : (G × G) × (G × G) => (p.1.1, p.2.1, p.1.2, p.2.2)) := by fun_prop
    exact hf.comp hg
  have h1 : Measurable fun x : G × G => ∫⁻ y, f x.1 y.1 x.2 y.2 ∂(ν'.prod μS') :=
    hm.lintegral_prod_right'
  calc ∫⁻ p, f p.1.1 p.2.1 p.1.2 p.2.2 ∂((ν.prod μS).prod (ν'.prod μS'))
      = ∫⁻ x, ∫⁻ y, f x.1 y.1 x.2 y.2 ∂(ν'.prod μS') ∂(ν.prod μS) :=
        lintegral_prod (fun p : (G × G) × (G × G) => f p.1.1 p.2.1 p.1.2 p.2.2) hm.aemeasurable
    _ = ∫⁻ z, ∫⁻ s, ∫⁻ y, f z y.1 s y.2 ∂(ν'.prod μS') ∂μS ∂ν :=
        lintegral_prod (fun x : G × G => ∫⁻ y, f x.1 y.1 x.2 y.2 ∂(ν'.prod μS')) h1.aemeasurable
    _ = ∫⁻ z, ∫⁻ s, ∫⁻ z', ∫⁻ s', f z z' s s' ∂μS' ∂ν' ∂μS ∂ν := by
        refine lintegral_congr fun z => lintegral_congr fun s => ?_
        have hg : Measurable (fun y : G × G => (z, y.1, s, y.2)) := by fun_prop
        exact lintegral_prod (fun y : G × G => f z y.1 s y.2) (hf.comp hg).aemeasurable
    _ = ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', f z z' s s' ∂μS' ∂μS ∂ν' ∂ν := by
        refine lintegral_congr fun z => ?_
        have hg : Measurable (fun p : (G × G) × G => (z, p.1.2, p.1.1, p.2)) := by fun_prop
        have hk : Measurable (fun p : (G × G) × G => f z p.1.2 p.1.1 p.2) := hf.comp hg
        have hk' : Measurable (fun x : G × G => ∫⁻ s', f z x.2 x.1 s' ∂μS') :=
          hk.lintegral_prod_right'
        exact lintegral_lintegral_swap (f := fun s z' => ∫⁻ s', f z z' s s' ∂μS') hk'.aemeasurable

theorem measurable_bInt {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun q : G × G × G × G => bInt σ w W W' γ q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold bInt
  have h1 : Measurable fun q : G × G × G × G =>
      ‖⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹) (σ q.2.1 w)⟫_ℂ‖ₑ :=
    (continuous_enorm.comp (continuous_coef5 hσ w γ)).measurable
  have h2 : Measurable fun q : G × G × G × G => ‖W q.1‖ₑ :=
    (continuous_enorm.comp (hW.comp continuous_fst)).measurable
  have h3 : Measurable fun q : G × G × G × G => ‖W' q.2.1‖ₑ :=
    (continuous_enorm.comp (hW'.comp (continuous_fst.comp continuous_snd))).measurable
  exact (h1.mul h2).mul h3

theorem ae_mem_four {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS'] {S S' : Set G}
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) :
    ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')), p.1.2 ∈ S ∧ p.2.2 ∈ S' := by
  have hS : ∀ᵐ s ∂μS, s ∈ S := ae_iff.mpr h0
  have hS' : ∀ᵐ s ∂μS', s ∈ S' := ae_iff.mpr h0'
  have a1 : ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')), p.1.2 ∈ S :=
    quasiMeasurePreserving_fst.ae (quasiMeasurePreserving_snd.ae hS)
  have a2 : ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')), p.2.2 ∈ S' :=
    quasiMeasurePreserving_snd.ae (quasiMeasurePreserving_snd.ae hS')
  exact a1.and a2

theorem prod_map_φinv {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) :
    μ.prod μ = ((ν.prod μS).prod (ν'.prod μS')).map (Prod.map φinv φinv) := by
  calc μ.prod μ = ((ν.prod μS).map φinv).prod ((ν'.prod μS').map φinv) := by
        rw [← hm, ← hm']
    _ = _ := map_prod_map _ _ measurable_φinv measurable_φinv

theorem enorm_kG_shift_le {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ ν ν' : Measure G} {d : ℝ} {w : HH}
    {S S' : Set G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (γ z u z' u' : G) (hu : u ∈ S) (hu' : u' ∈ S') :
    ‖kG σ d w W W' γ (u⁻¹ * z, u'⁻¹ * z')‖ₑ ≤ ‖(d : ℂ)‖ₑ * bInt σ w W W' γ z z' u u' := by
  have e1 : ‖W (u⁻¹ * z)‖ₑ = ‖W z‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    exact NNReal.eq ((norm_W_shift hW) hinv hu z)
  have e2 : ‖W' (u'⁻¹ * z')‖ₑ = ‖W' z'‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    exact NNReal.eq ((norm_W_shift hW') hinv' hu' z')
  have hR : ‖Formalism.L2.SG.Pf.EnergyAbs.rk1A (W (u⁻¹ * z)) (W' (u'⁻¹ * z'))‖ₑ ≤ ‖W z‖ₑ * ‖W' z'‖ₑ := by
    rw [← e1, ← e2]
    exact enorm_rk1A_le _ _
  simp only [kG, bInt]
  rw [coef_shift hσ, enorm_smul, enorm_mul]
  calc ‖(d : ℂ)‖ₑ * ‖⟪σ z w, σ (u * γ * u'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖Formalism.L2.SG.Pf.EnergyAbs.rk1A (W (u⁻¹ * z)) (W' (u'⁻¹ * z'))‖ₑ
      ≤ ‖(d : ℂ)‖ₑ * ‖⟪σ z w, σ (u * γ * u'⁻¹) (σ z' w)⟫_ℂ‖ₑ * (‖W z‖ₑ * ‖W' z'‖ₑ) := by gcongr
    _ = _ := by simp only [mul_assoc]

private theorem ae_enorm_kG_le_bInt {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS]
    [SFinite ν'] [SFinite μS'] {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) {μ : Measure G} {d : ℝ}
    {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : Formalism.L2.SG.Pf.EnergyAbs.IsWAbs μ σ d w S τ ν W) (hW' : Formalism.L2.SG.Pf.EnergyAbs.IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (γ : G) :
    ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')),
      ‖kG σ d w W W' γ (p.1.2⁻¹ * p.1.1, p.2.2⁻¹ * p.2.1)‖ₑ ≤
        ‖(d : ℂ)‖ₑ * bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2 := by
  have hmem := ae_mem_four (ν := ν) (ν' := ν') h0 h0'
  refine hmem.mono fun p hp => ?_
  exact enorm_kG_shift_le hσ hW hW' hinv hinv' γ p.1.1 p.1.2 p.2.1 p.2.2 hp.1 hp.2

private theorem measurable_bInt_prod {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) (w : HH)
    {W : G → V} {W' : G → V'} (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun p : (G × G) × (G × G) => bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2) := by
  obtain ⟨-, hmul, -, hc⟩ := hσ
  have e : (fun p : (G × G) × (G × G) => bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2) =
      fun p => ‖⟪σ p.1.1 w, σ (p.1.2 * γ * p.2.2⁻¹ * p.2.1) w⟫_ℂ‖ₑ * ‖W p.1.1‖ₑ * ‖W' p.2.1‖ₑ := by
    funext p
    unfold bInt
    rw [hmul (p.1.2 * γ * p.2.2⁻¹) p.2.1, ContinuousLinearMap.mul_apply]
  rw [e]
  have hg : Continuous fun p : (G × G) × (G × G) => p.1.2 * γ * p.2.2⁻¹ * p.2.1 := by fun_prop
  have h1 : Measurable fun p : (G × G) × (G × G) =>
      ‖⟪σ p.1.1 w, σ (p.1.2 * γ * p.2.2⁻¹ * p.2.1) w⟫_ℂ‖ₑ :=
    (continuous_enorm.comp
      (((hc w).comp (continuous_fst.comp continuous_fst)).inner ((hc w).comp hg))).measurable
  have h2 : Measurable fun p : (G × G) × (G × G) => ‖W p.1.1‖ₑ :=
    (continuous_enorm.comp (hW.comp (continuous_fst.comp continuous_fst))).measurable
  have h3 : Measurable fun p : (G × G) × (G × G) => ‖W' p.2.1‖ₑ :=
    (continuous_enorm.comp (hW'.comp (continuous_fst.comp continuous_snd))).measurable
  exact (h1.mul h2).mul h3

set_option maxHeartbeats 800000 in

private theorem lintegral_const_mul_bInt_eq_iterated {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS]
    [SFinite ν'] [SFinite μS'] {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) (w : HH) {W : G → V}
    {W' : G → V'} (hW : Continuous W) (hW' : Continuous W') (γ : G) (c : ℝ≥0∞) :
    ∫⁻ p : (G × G) × (G × G), c * bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2
        ∂((ν.prod μS).prod (ν'.prod μS')) =
      c * ∫⁻ z : G, ∫⁻ z' : G, ∫⁻ s : G, ∫⁻ s' : G, bInt σ w W W' γ z z' s s'
        ∂μS' ∂μS ∂ν' ∂ν := by
  have hc := measurable_bInt_prod hσ w hW hW' γ
  have e1 := lintegral_const_mul (μ := (ν.prod μS).prod (ν'.prod μS')) c hc
  have e2 := lintegral_four (ν := ν) (μS := μS) (ν' := ν') (μS' := μS')
    (bInt σ w W W' γ) (measurable_bInt hσ w hW hW' γ)
  exact e1.trans (congrArg (fun x => c * x) e2)

theorem lintegral_kG_shift_lt_top {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ : Measure G} {d : ℝ} {w : HH} {S S' : Set G}
    {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ∫⁻ p, ‖kG σ d w W W' γ (p.1.2⁻¹ * p.1.1, p.2.2⁻¹ * p.2.1)‖ₑ ∂((ν.prod μS).prod (ν'.prod μS')) < ⊤ := by
  have hle := ae_enorm_kG_le_bInt hσ hW hW' hinv hinv' h0 h0' γ
  have h2 := lintegral_const_mul_bInt_eq_iterated (ν := ν) (μS := μS) (ν' := ν') (μS' := μS') hσ w
    hW.2.2.2.2.1 hW'.2.2.2.2.1 γ ‖(d : ℂ)‖ₑ
  have hd : ‖(d : ℂ)‖ₑ ≠ ⊤ := enorm_ne_top
  refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
  rw [h2]
  exact (ENNReal.mul_ne_top hd hB.ne).lt_top

theorem integrable_kG {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
    {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    Integrable (kG σ d w W W' γ) (μ.prod μ) := by
  have hK : Continuous (kG σ d w W W' γ) :=
    continuous_kG hσ d w hW.2.2.2.2.1 hW'.2.2.2.2.1 γ
  refine ⟨hK.aestronglyMeasurable, ?_⟩
  have hF : Measurable (Prod.map φinv φinv : (G × G) × (G × G) → G × G) :=
    (continuous_φinv.prodMap continuous_φinv).measurable
  have hg : Measurable fun q : G × G => ‖kG σ d w W W' γ q‖ₑ :=
    (continuous_enorm.comp hK).measurable
  show ∫⁻ q, ‖kG σ d w W W' γ q‖ₑ ∂(μ.prod μ) < ⊤
  rw [prod_map_φinv hm hm', lintegral_map hg hF]
  exact lintegral_kG_shift_lt_top hσ hW hW' hinv hinv' h0 h0' γ hB

end Formalism.L2.S.Pv.EnergyAbs

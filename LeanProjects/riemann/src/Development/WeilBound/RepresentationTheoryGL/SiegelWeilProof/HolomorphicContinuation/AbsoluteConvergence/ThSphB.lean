import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphSt

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem integrable_of_cpt {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [IsFiniteMeasure μ] (hK : IsCompact (univ : Set K)) {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun _ _ => measure_lt_top μ _⟩
  exact hf.integrable_of_hasCompactSupport (hK.of_isClosed_subset (isClosed_tsupport f) (subset_univ _))

theorem finInt {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (hK : IsCompact (univ : Set K)) {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (v : K → V) (hv : ∀ k, v k ∈ W) (hc : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun k => l (v k))
    (w : K → ℂ) (hw : Continuous w) : ∃ Φ : V, ∀ l : V →ₗ[ℂ] ℂ, l Φ = ∫ k, w k * l (v k) ∂μ := by
  classical
  let b := Module.finBasis ℂ W
  have hext : ∀ i, ∃ L : V →ₗ[ℂ] ℂ, ∀ x : W, L x = b.repr x i := fun i => by
    obtain ⟨L, hL⟩ := LinearMap.exists_extend (b.coord i)
    exact ⟨L, fun x => by simpa using congrArg (fun f => f x) hL⟩
  choose L hL using hext
  refine ⟨∑ i, (∫ k, w k * L i (v k) ∂μ) • (b i : V), fun l => ?_⟩
  have hv' : ∀ k, l (v k) = ∑ i, L i (v k) * l (b i) := by
    intro k
    have h1 := b.sum_repr ⟨v k, hv k⟩
    have h2 : v k = ∑ i, (b.repr ⟨v k, hv k⟩ i) • (b i : V) := by
      have h3 := congrArg Subtype.val h1
      rw [Submodule.coe_sum] at h3
      simp only [Submodule.coe_smul] at h3
      exact h3.symm
    conv_lhs => rw [h2]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, ← hL i ⟨v k, hv k⟩]
  rw [map_sum]
  simp_rw [map_smul, smul_eq_mul]
  have hint : ∀ i, Integrable (fun k => w k * L i (v k) * l (b i)) μ := fun i =>
    integrable_of_cpt μ hK ((hw.mul (hc (L i))).mul continuous_const)
  calc ∑ i, (∫ k, w k * L i (v k) ∂μ) * l (b i) = ∑ i, ∫ k, w k * L i (v k) * l (b i) ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_mul_const]
    _ = ∫ k, ∑ i, w k * L i (v k) * l (b i) ∂μ := (integral_finsetSum _ fun i _ => hint i).symm
    _ = ∫ k, w k * l (v k) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hv' k, Finset.mul_sum, mul_assoc]

set_option maxHeartbeats 4000000 in

theorem thSph_of' (hA : HelpA) (hC : HelpC) (hKAK : KAK) (hMult : Mult) (hD : DerivativeVacuumDilations) (hSph : Sph)
    (hSZ : SecZero) (hHP : HolParam) (hLC : LC) : ThSph := by
  intro m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG _ _ μ _ _ g y
  obtain ⟨hAdil, hAuniq, hAcpt, _hAdet, hAF0c, hAV, hAF0⟩ := hA
  obtain ⟨hCrc, hCzero⟩ := hC
  have hKc : IsCompact (univ : Set (KR n)) := hAcpt n
  have hF0 : Continuous (F0 (n := n) p q e) := (hAF0 n p q e).1
  have hF0ne : ∀ k : KR n, F0 p q e (k : GR n) ≠ 0 := fun k => (hAF0 n p q e).2 k k.2
  have hw : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ := (hF0.comp continuous_subtype_val).inv₀ hF0ne
  have hF01 : F0 (n := n) p q e 1 = 1 := by
    have h := ((hMult n p q e).1 1 1 (KR n).one_mem).1
    rw [mul_one] at h
    have hne : F0 (n := n) p q e 1 ≠ 0 := by simpa using hF0ne 1
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact h.symm)
  have hRI : ∀ (z k2 : GR n), k2 ∈ KR n →
      (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (z * k2))) ∂μ) =
        F0 p q e k2 * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * z)) ∂μ := by
    intro z k2 hk2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have hk2' : InK (mR k2) := hk2
    have h1 : I 1 (g * ι ((k : GR n) * (z * k2))) = F0 p q e k2 * I 1 (g * ι ((k : GR n) * z)) := by
      rw [← mul_assoc, map_mul ι, ← mul_assoc g, hG.Ik 1 _ k2 hk2', hL.kvac k2 hk2', map_smul]
      rfl
    simp only [h1]
    ring
  have hRS : ∀ (z k2 : GR n), k2 ∈ KR n →
      (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (z * k2)) ∂μ) =
        F0 p q e k2 * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * z) ∂μ := by
    intro z k2 hk2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [← mul_assoc, ((hMult n p q e).1 _ k2 hk2).1]
    ring
  have key : ∀ (k1 : GR n), k1 ∈ KR n → ∀ (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
      (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) ∂μ) =
        I 1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)) ∂μ := by
    intro k1 hk1 X a ha
    obtain ⟨U, F, hUo, hUR, hFc, hF⟩ := hG.Idil g X a ha
    have hmc : Continuous fun k : KR n => (k : GR n) * k1 := continuous_subtype_val.mul continuous_const
    obtain ⟨V, hVo, hVR, hVc, hVd⟩ := hAV n p q e X _ (hKc.image hmc)
    have hKm : ∀ k : KR n, (k : GR n) * k1 ∈ KR n := fun k => (KR n).mul_mem k.2 hk1
    have hSm : ∀ k : KR n, (k : GR n) * k1 ∈ (fun k : KR n => (k : GR n) * k1) '' univ :=
      fun k => mem_image_of_mem _ (mem_univ _)
    have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0
    have h0V : (0 : ℂ) ∈ V := by simpa using hVR 0
    set Q : PX m n := (dil c X ^ 0) 1 with hQ0
    let Gk : KR n → ℂ → ℂ := fun k z => (F0 p q e (k : GR n))⁻¹ *
      (F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z)
    have hpm : Continuous fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2) :=
      (hmc.comp continuous_fst).prodMk continuous_snd
    have hc1 : ContinuousOn (fun w : KR n × ℂ => F ((w.1 : GR n) * k1) w.2) (univ ×ˢ (U ∩ V)) :=
      ContinuousOn.comp (f := fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2)) (g := fun y : GR n × ℂ => F y.1 y.2)
        hFc hpm.continuousOn (fun w hw' => ⟨mem_univ _, hw'.2.1⟩)
    have hc2 : ContinuousOn (fun w : KR n × ℂ => holomorphicSectionExtension p q e X ((w.1 : GR n) * k1) w.2) (univ ×ˢ (U ∩ V)) :=
      ContinuousOn.comp (f := fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2))
        (g := fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) hVc hpm.continuousOn (fun w hw' => ⟨hSm w.1, hw'.2.2⟩)
    have hGc : ContinuousOn (fun w : KR n × ℂ => Gk w.1 w.2) (univ ×ˢ (U ∩ V)) :=
      ((hw.comp continuous_fst).continuousOn).mul (hc1.sub (continuousOn_const.mul hc2))
    have hGd : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (Gk k) (U ∩ V) := by
      intro k _
      refine DifferentiableOn.const_mul (DifferentiableOn.sub ?_ (DifferentiableOn.const_mul ?_ _)) _
      · exact ((hF _).1).mono inter_subset_left
      · exact (hVd _ (hSm k)).mono inter_subset_right
    obtain ⟨hφd, hφD⟩ := hHP (KR n) μ univ hKc (by simp) (U ∩ V) Gk (hUo.inter hVo) hGc hGd
    have hder : ∀ r : ℕ, iteratedDeriv r (fun z => ∫ k, Gk k z ∂μ) 0 = 0 := by
      intro r
      rw [hφD 0 ⟨h0U, h0V⟩ r]
      set Qr : PX m n := (dil c X ^ r) 1 with hQr
      obtain ⟨W, hWf, hQW, hWst, hWc⟩ := hL.kfin Qr
      haveI := hWf
      have hvW : ∀ k : KR n, ρ ((k : GR n) * k1) Qr ∈ W := fun k => hWst _ (hKm k) Qr hQW
      have hvc : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous fun k : KR n => l (ρ ((k : GR n) * k1) Qr) := fun l =>
        (hWc Qr hQW l).comp_continuous hmc (fun k => hKm k)
      obtain ⟨Φ, hΦ⟩ := finInt μ hKc W (fun k : KR n => ρ ((k : GR n) * k1) Qr) hvW hvc _ hw

      have hval : ∀ k : KR n, iteratedDeriv r (Gk k) 0 = (F0 p q e (k : GR n))⁻¹ *
          (I (ρ ((k : GR n) * k1) Qr) g - I 1 g * sL (ρ ((k : GR n) * k1) Qr) 1) := by
        intro k
        have hcF : ContDiffAt ℂ r (F ((k : GR n) * k1)) 0 :=
          ((hF _).1.contDiffOn hUo).contDiffAt (hUo.mem_nhds h0U)
        have hcG : ContDiffAt ℂ r (fun z => I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) 0 :=
          contDiffAt_const.mul (((hVd _ (hSm k)).contDiffOn hVo).contDiffAt (hVo.mem_nhds h0V))
        have e1 : iteratedDeriv r (Gk k) 0 = (F0 p q e (k : GR n))⁻¹ *
            iteratedDeriv r (fun z => F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) 0 := by
          simp only [Gk]
          rw [iteratedDeriv_const_mul_field]
        have e0 : (fun z => F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) =
            F ((k : GR n) * k1) - fun z => I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z := rfl
        rw [e1, e0, iteratedDeriv_sub hcF hcG]
        simp only [iteratedDeriv_const_mul_field]
        rw [(hF _).2.2 r, hG.Ik Qr g _ (hKm k)]
        have e2 : iteratedDeriv r (holomorphicSectionExtension p q e X ((k : GR n) * k1)) 0 = sL (ρ ((k : GR n) * k1) Qr) 1 := by
          have h3 := hCrc (holomorphicSectionExtension p q e X ((k : GR n) * k1)) V hVo hVR (hVd _ (hSm k)) r 0
          simp only [Complex.ofReal_zero] at h3
          rw [← h3]
          have h4 : (fun t : ℝ => holomorphicSectionExtension p q e X ((k : GR n) * k1) t) = fun s => F0 p q e ((k : GR n) * k1 * a s) :=
            funext fun s => hAF0c n p q e X a ha _ s
          rw [h4, (hD m n ε c t p q e sL ρ hL X a ha _ r).2]
          rw [← hL.kact Qr 1 _ (hKm k), one_mul]
        rw [e2]
      let lg : PX m n →ₗ[ℂ] ℂ := (LinearMap.proj g).comp I
      let ly : GR n → PX m n →ₗ[ℂ] ℂ := fun y' => (LinearMap.proj y').comp sL
      have hlg : ∀ P, lg P = I P g := fun P => rfl
      have hly : ∀ y' P, ly y' P = sL P y' := fun y' P => rfl
      have hcv : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * l (ρ ((k : GR n) * k1) Qr) :=
        fun l => hw.mul (hvc l)

      set D : ℂ := iteratedDeriv r (fun s : ℝ => ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
        F0 p q e ((k : GR n) * (k1 * a s)) ∂μ) 0 with hDdef
      have hsL : ∀ y' : GR n, sL Φ y' = F0 p q e y' * D := by
        intro y'
        have hm' : Continuous fun k : KR n => y' * ((k : GR n) * k1) := continuous_const.mul hmc
        obtain ⟨V', hV'o, hV'R, hV'c, hV'd⟩ := hAV n p q e X _ (hKc.image hm')
        have hSm' : ∀ k : KR n, y' * ((k : GR n) * k1) ∈ (fun k : KR n => y' * ((k : GR n) * k1)) '' univ :=
          fun k => mem_image_of_mem _ (mem_univ _)
        have h0V' : (0 : ℂ) ∈ V' := by simpa using hV'R 0
        let Gk' : KR n → ℂ → ℂ := fun k z => (F0 p q e (k : GR n))⁻¹ * holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1)) z
        have hpm' : Continuous fun w : KR n × ℂ => (y' * ((w.1 : GR n) * k1), w.2) :=
          (hm'.comp continuous_fst).prodMk continuous_snd
        have hc3 : ContinuousOn (fun w : KR n × ℂ => holomorphicSectionExtension p q e X (y' * ((w.1 : GR n) * k1)) w.2) (univ ×ˢ V') :=
          ContinuousOn.comp (f := fun w : KR n × ℂ => (y' * ((w.1 : GR n) * k1), w.2))
            (g := fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) hV'c hpm'.continuousOn (fun w hw' => ⟨hSm' w.1, hw'.2⟩)
        have hGc' : ContinuousOn (fun w : KR n × ℂ => Gk' w.1 w.2) (univ ×ˢ V') :=
          ((hw.comp continuous_fst).continuousOn).mul hc3
        have hGd' : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (Gk' k) V' := fun k _ =>
          (hV'd _ (hSm' k)).const_mul _
        obtain ⟨hψd, hψD⟩ := hHP (KR n) μ univ hKc (by simp) V' Gk' hV'o hGc' hGd'
        have step1 : sL Φ y' = ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
            iteratedDeriv r (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) 0 ∂μ := by
          rw [← hly, hΦ (ly y')]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [hly]
          rw [← hL.kact Qr y' _ (hKm k), ← (hD m n ε c t p q e sL ρ hL X a ha _ r).2]
          have h3 := hCrc (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) V' hV'o hV'R (hV'd _ (hSm' k)) r 0
          simp only [Complex.ofReal_zero] at h3
          rw [← h3]
          congr 2
          funext s
          exact (hAF0c n p q e X a ha _ s).symm
        have step2 : (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
            iteratedDeriv r (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) 0 ∂μ) =
            iteratedDeriv r (fun z => ∫ k, Gk' k z ∂μ) 0 := by
          rw [hψD 0 h0V' r]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [Gk', iteratedDeriv_const_mul_field]
        have step3 : iteratedDeriv r (fun z => ∫ k, Gk' k z ∂μ) 0 =
            iteratedDeriv r (fun t : ℝ => ∫ k, Gk' k t ∂μ) 0 := by
          have h3 := hCrc _ V' hV'o hV'R hψd r 0
          simp only [Complex.ofReal_zero] at h3
          exact h3.symm
        have step4 : (fun t : ℝ => ∫ k, Gk' k t ∂μ) = fun t : ℝ => F0 p q e y' *
            ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a t)) ∂μ := by
          funext t
          rw [← hSph n p q e μ y' (k1 * a t)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [Gk']
          rw [hAF0c n p q e X a ha _ t]
          simp only [mul_assoc]
        rw [step1, step2, step3, step4, iteratedDeriv_const_mul_field]
      have hν : sL Φ 1 = D := by rw [hsL 1, hF01, one_mul]
      have hnull : NullSec ε c (Φ - D • 1) := by
        refine (hSZ m n ε c t p q e sL ρ hL (Φ - D • 1)).mpr fun y' => ?_
        rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsL y', hL.vac y']
        ring
      have hLC' := hLC m n ε c hL.cpos lg (fun a b P => hG.Iinv g a b P) _ hnull
      rw [map_sub, map_smul, smul_eq_mul, hlg, hlg] at hLC'
      have hint1 := integrable_of_cpt μ hKc (hcv lg)
      have hint2 := integrable_of_cpt μ hKc (hcv (ly 1))
      calc (∫ k : KR n, iteratedDeriv r (Gk k) 0 ∂μ)
          = ∫ k : KR n, ((F0 p q e (k : GR n))⁻¹ * lg (ρ ((k : GR n) * k1) Qr) -
              I 1 g * ((F0 p q e (k : GR n))⁻¹ * ly 1 (ρ ((k : GR n) * k1) Qr))) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
            dsimp only
            rw [hval k, hlg, hly]
            ring
        _ = lg Φ - I 1 g * ly 1 Φ := by
            rw [integral_sub hint1 (hint2.const_mul _), integral_const_mul, hΦ lg, hΦ (ly 1)]
        _ = 0 := by
            rw [hlg, hly, hν]
            linear_combination hLC'
    have hz := hCzero (fun z => ∫ k, Gk k z ∂μ) (U ∩ V) (hUo.inter hVo) (fun s => ⟨hUR s, hVR s⟩) hφd hder 1
    have hcI : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) :=
      hw.mul (hG.Icont.comp (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const))))
    have hcS : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)) :=
      hw.mul (hF0.comp (continuous_subtype_val.mul continuous_const))
    have hz' : (∫ k : KR n, ((F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) -
        I 1 g * ((F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)))) ∂μ) = 0 := by
      rw [← hz]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [Gk]
      rw [(hF _).2.1 1, hAF0c n p q e X a ha _ 1]
      simp only [mul_assoc]
      ring
    rw [integral_sub (integrable_of_cpt μ hKc hcI) ((integrable_of_cpt μ hKc hcS).const_mul _),
      integral_const_mul] at hz'
    exact sub_eq_zero.mp hz'
  obtain ⟨k1, k2, a1, X, hk1, hk2, hda1, rfl⟩ := hKAK n y
  obtain ⟨a, ha⟩ := hAdil n X
  have ha1 : a1 = a 1 := hAuniq n X 1 a1 (a 1) hda1 (ha 1)
  subst ha1
  rw [hRI _ k2 hk2, hRS _ k2 hk2, key k1 hk1 X a ha]
  ring

end PositivityTheory.Rg.Sw.AbsSt

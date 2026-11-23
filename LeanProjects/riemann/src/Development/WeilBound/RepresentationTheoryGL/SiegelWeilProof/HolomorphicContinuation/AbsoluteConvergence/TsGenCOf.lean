import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TwistedScalarSection
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IteratedDerivOfReal
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IteratedDerivSumOn
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousOnTwistedSectionCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SphericalCharacterInvMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMemFinDimSubspace

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

set_option maxHeartbeats 1600000 in
theorem tsGenC_of (hD : CayleyBlocksInvertible) (hK : KAK) (hM : Mult) (hS : SecZero) (hDF : DerivativeVacuumDilations)
    (hH : HolParam) (hLC : LC) (hT : TSBFacts) : TSGenC := by
  intro m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I hG _ _ W hWf hWρ ν κ hν hκ hfix hproj gpt y Q hQW hQ
  haveI := hν
  haveI : FiniteDimensional ℂ W := hWf
  obtain ⟨hKc, hmRc, hF0c, hdilex, hdilmat, hext⟩ := hT hD n p q e
  haveI := hKc
  have hc0 : 0 < c := hL.cpos
  have hIsec : ∀ Q1 Q2 : PX m n, (∀ y', sL Q1 y' = sL Q2 y') → I Q1 gpt = I Q2 gpt := by
    intro Q1 Q2 h12
    have hnull : NullSec ε c (Q1 - Q2) :=
      (hS m n ε c t p q e sL ρ hL (Q1 - Q2)).2 (fun y' => by simp [map_sub, h12 y'])
    have h0 := hLC m n ε c hc0 ((LinearMap.proj gpt).comp I)
      (fun a b P => by simpa using hG.Iinv gpt a b P) (Q1 - Q2) hnull
    have h1 : I Q1 gpt - I Q2 gpt = 0 := by simpa [map_sub] using h0
    exact sub_eq_zero.1 h1
  have hπ : ∀ f : GR n → ℂ, Continuous f → (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = F0 p q e y * f g) →
      ∃ Q1 ∈ W, ∀ y', ∫ k, κ k * f (y' * (k : GR n)) ∂ν = sL Q1 y' := by
    intro f hf hlaw
    obtain ⟨Q1, hQ1, h1⟩ := hproj 0 f hf (fun y g hy => by rw [hlaw y g hy]; simp)
    exact ⟨Q1, hQ1, fun y' => by rw [h1 y']; simp⟩
  obtain ⟨k1, k2, a, X, hk1, hk2, ha, rfl⟩ := hK n y
  have hF2 : F0 p q e k2 ≠ 0 := right_ne_zero_of_mul_eq_one (spherical_character_inv_mul hM n p q e k2 hk2)
  have key : ∀ Q' ∈ W, (∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * (k1 * a)) ∂ν = sL Q' y') →
      ∫ k, κ k * I 1 (gpt * ι ((k : GR n) * (k1 * a))) ∂ν = I Q' gpt := by
    intro Q' hQ'W hQ'
    choose af haf using hdilex X
    have ha1 : af 1 = a := by
      apply Subtype.ext
      apply Units.ext
      show mR (af 1) = mR a
      rw [hdilmat X 1 (af 1) (haf 1), hdilmat X 1 a ha]
    obtain ⟨U1, Fid, hU1o, hU1R, hFidc, hFid⟩ := hG.Idil gpt X af haf

    let V : Submodule ℂ (GR n → ℂ) := W.map sL
    obtain ⟨Bm, hBm⟩ := LinearMap.exists_rightInverse_of_surjective (LinearMap.submoduleMap sL W)
      (LinearMap.range_eq_top.2 (LinearMap.submoduleMap_surjective sL W))
    let ℓ : Module.Dual ℂ V := ((LinearMap.proj gpt).comp I).comp (W.subtype.comp Bm)
    have hℓ : ∀ (v : V) (Q1 : PX m n), (∀ y', sL Q1 y' = (v : GR n → ℂ) y') → ℓ v = I Q1 gpt := by
      intro v Q1 h1
      have hv : (LinearMap.submoduleMap sL W) (Bm v) = v := LinearMap.congr_fun hBm v
      have hv' : sL ((Bm v : W) : PX m n) = (v : GR n → ℂ) := by
        have := congrArg (fun w : V => (w : GR n → ℂ)) hv
        simpa [LinearMap.submoduleMap] using this
      show I ((Bm v : W) : PX m n) gpt = I Q1 gpt
      exact hIsec _ _ (fun y' => by rw [hv', h1 y'])
    have hspan := GlobalTheory.dual_mem_span_eval_of_finiteDimensional V ℓ
    obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hspan
    have hℓeval : ∀ v : V, ℓ v = ∑ y ∈ cf.support, cf y * (v : GR n → ℂ) y := by
      intro v
      rw [← hcf]
      simp [Finsupp.sum, LinearMap.sum_apply]

    set S := cf.support
    let C : Set (GR n) := ⋃ y ∈ S, range (fun k : KR n => y * (k : GR n) * k1)
    have hCc : IsCompact C := S.isCompact_biUnion fun y _ =>
      isCompact_range (cont_KR_mul n y k1)
    have hmemC : ∀ y ∈ S, ∀ k : KR n, y * (k : GR n) * k1 ∈ C := fun y hy k =>
      mem_biUnion hy ⟨k, rfl⟩
    obtain ⟨U2, hU2o, hU2R, hU2c, hU2d⟩ := hext X C hCc
    set U := U1 ∩ U2 with hUdef
    have hUo : IsOpen U := hU1o.inter hU2o
    have hUR : ∀ x : ℝ, (x : ℂ) ∈ U := fun x => ⟨hU1R x, hU2R x⟩
    have hcomp : IsCompact (univ : Set (KR n)) := isCompact_univ
    have hnull : ν (univ : Set (KR n))ᶜ = 0 := by simp

    have hFlc : ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * Fid ((yz.1 : GR n) * k1) yz.2) (univ ×ˢ U) :=
      contOn_Fid k1 U U1 inter_subset_left κ hκ Fid hFidc
    have hFld : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (fun z => κ k * Fid ((k : GR n) * k1) z) U := by
      intro k _
      exact (((hFid ((k : GR n) * k1)).1.mono inter_subset_left).const_mul (κ k))
    obtain ⟨hLd, hLr⟩ := hH (KR n) ν univ hcomp hnull U (fun k z => κ k * Fid ((k : GR n) * k1) z) hUo hFlc hFld

    have hFrc : ∀ y ∈ S, ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2))
        (univ ×ˢ U) := fun y hy =>
      continuousOn_twisted_section_compact p q e X y k1 U κ hκ C (hmemC y hy) (hU2c.mono (prod_mono subset_rfl inter_subset_right))
    have hFrd : ∀ y ∈ S, ∀ k ∈ (univ : Set (KR n)),
        DifferentiableOn ℂ (fun z => κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z)) U := by
      intro y hy k _
      exact (((hU2d _ (hmemC y hy k)).mono inter_subset_right).const_mul (κ k))
    have hRy : ∀ y ∈ S, DifferentiableOn ℂ (fun z => ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν) U ∧
        ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν) z = ∫ k, iteratedDeriv r (fun z => κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z)) z ∂ν :=
      fun y hy => hH (KR n) ν univ hcomp hnull U (fun k z => κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z)) hUo (hFrc y hy) (hFrd y hy)
    let Lt : ℂ → ℂ := fun z => ∫ k, κ k * Fid ((k : GR n) * k1) z ∂ν
    let Rt : ℂ → ℂ := fun z => ∑ y ∈ S, cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν
    have hRd : DifferentiableOn ℂ Rt U := by
      have h := DifferentiableOn.sum (u := S)
        (A := fun y z => cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν)
        (fun y hy => (hRy y hy).1.const_mul (cf y))
      have heq : (∑ y ∈ S, fun z => cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν) = Rt := by
        ext z
        simp only [Finset.sum_apply]
        rfl
      rwa [heq] at h
    have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0

    have hder : ∀ r : ℕ, iteratedDeriv r Lt 0 = iteratedDeriv r Rt 0 := by
      intro r
      set Q0 : PX m n := (dil c X ^ r) 1
      obtain ⟨Wr, hWrf, hQ0Wr, hWrρ, hWrc⟩ := hL.kfin Q0
      haveI : FiniteDimensional ℂ Wr := hWrf
      have hinK : ∀ k : KR n, InK (mR ((k : GR n) * k1)) := fun k => inK_mul k k1 hk1

      have hcont_l : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous (fun k : KR n => κ k * l (ρ ((k : GR n) * k1) Q0)) := by
        intro l
        refine hκ.mul ?_
        have h1 := hWrc Q0 hQ0Wr l
        exact h1.comp_continuous (cont_KR_mul' n k1) (fun k => hinK k)
      obtain ⟨Φ, hΦW, hΦ⟩ := TSC.exists_int_elem ν Wr (fun k : KR n => κ k • ρ ((k : GR n) * k1) Q0)
        (fun k => Wr.smul_mem _ (hWrρ _ (hinK k) Q0 hQ0Wr))
        (fun l => by
          have := (hcont_l l).continuousOn.integrableOn_compact (μ := ν) hcomp
          simpa [map_smul, smul_eq_mul] using integrableOn_univ.1 this)

      obtain ⟨Qr, hQrW, hQr⟩ := hπ (fun y' => sL Q0 (y' * k1)) ((hL.cont Q0).comp (continuous_id.mul continuous_const))
        (fun y g hy => by
          show sL Q0 (y * g * k1) = F0 p q e y * sL Q0 (g * k1)
          rw [mul_assoc, hL.law Q0 y (g * k1) hy])
      have hsecΦ : ∀ y', sL Φ y' = sL Qr y' := by
        intro y'
        have h1 := hΦ ((LinearMap.proj y').comp sL)
        simp only [LinearMap.comp_apply, LinearMap.proj_apply, map_smul, Pi.smul_apply, smul_eq_mul] at h1
        rw [h1, ← hQr y']
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only
        rw [← hL.kact Q0 y' _ (hinK k), mul_assoc]
      have hIΦ : I Φ gpt = ∫ k, κ k * I (ρ ((k : GR n) * k1) Q0) gpt ∂ν := by
        have h1 := hΦ ((LinearMap.proj gpt).comp I)
        simpa [map_smul, smul_eq_mul] using h1

      have hL0 : iteratedDeriv r Lt 0 = I Qr gpt := by
        rw [show iteratedDeriv r Lt 0 = ∫ k, iteratedDeriv r (fun z => κ k * Fid ((k : GR n) * k1) z) 0 ∂ν
          from hLr 0 h0U r]
        have e1 : ∀ k : KR n, iteratedDeriv r (fun z => κ k * Fid ((k : GR n) * k1) z) 0 =
            κ k * I (ρ ((k : GR n) * k1) Q0) gpt := by
          intro k
          rw [iteratedDeriv_const_mul_field, (hFid ((k : GR n) * k1)).2.2 r, hG.Ik _ gpt _ (hinK k)]
        simp_rw [e1]
        rw [← hIΦ]
        exact hIsec _ _ hsecΦ

      have hR0 : iteratedDeriv r Rt 0 = I Qr gpt := by
        have hsum := (TSC.iteratedDeriv_sum_on S hUo (fun y z => cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν)
          (fun y hy => (hRy y hy).1.const_mul (cf y)) r).2 h0U
        beta_reduce at hsum
        rw [show Rt = fun w => ∑ y ∈ S, cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X w) ∂ν from rfl, hsum]
        have e2 : ∀ y ∈ S, iteratedDeriv r (fun z => cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X z) ∂ν) 0 =
            cf y * sL Qr y := by
          intro y hy
          rw [iteratedDeriv_const_mul_field, (hRy y hy).2 0 h0U r, ← hQr y]
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only
          rw [iteratedDeriv_const_mul_field]
          congr 1
          have hreal := (TSA.iteratedDeriv_ofReal' hU2o (hU2d _ (hmemC y hy k)) hU2R
            (h := fun s : ℝ => F0 p q e (y * (k : GR n) * k1 * af s))
            (fun s => by
              rw [spherical_section_eq_extension, mR_mul (y * (k : GR n) * k1) (af s), hdilmat X s (af s) (haf s)]) r).2 0
          simp only [Complex.ofReal_zero] at hreal
          rw [hreal, (hDF m n ε c t p q e sL ρ hL X af haf (y * (k : GR n) * k1) r).2]
        rw [Finset.sum_congr rfl e2]
        rw [← hℓ ⟨sL Qr, ⟨Qr, hQrW, rfl⟩⟩ Qr (fun _ => rfl), hℓeval]
      rw [hL0, hR0]

    have hLd' : DifferentiableOn ℂ Lt U := hLd
    have hval : Lt 1 = Rt 1 := by
      have h := TSA.eq_of_iteratedDeriv (f := Lt) (g := Rt) hUo hUR hLd' hRd hder 1
      simpa using h
    have hLt1 : Lt 1 = ∫ k, κ k * I 1 (gpt * ι ((k : GR n) * (k1 * a))) ∂ν := by
      show ∫ k, κ k * Fid ((k : GR n) * k1) 1 ∂ν = _
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only
      have := (hFid ((k : GR n) * k1)).2.1 1
      simp only [Complex.ofReal_one] at this
      rw [this, ha1, mul_assoc]
    have hRt1 : Rt 1 = I Q' gpt := by
      have e3 : ∀ y ∈ S, cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X 1) ∂ν = cf y * sL Q' y := by
        intro y hy
        rw [← hQ' y]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only
        have hm : aZ X (1 : ℂ) = mR a := by rw [hdilmat X 1 a ha]; simp
        rw [hm, ← mR_mul, ← spherical_section_eq_extension, mul_assoc (y * (k : GR n)) k1 a]
      show ∑ y ∈ S, cf y * ∫ k, κ k * twistedScalarSection p q e (mR (y * (k : GR n) * k1) * aZ X 1) ∂ν = I Q' gpt
      rw [Finset.sum_congr rfl e3, ← hℓeval ⟨sL Q', ⟨Q', hQ'W, rfl⟩⟩]
      exact hℓ _ Q' (fun _ => rfl)
    rw [← hLt1, hval, hRt1]

  have hQ' : ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * (k1 * a)) ∂ν = sL ((F0 p q e k2)⁻¹ • Q) y' := by
    intro y'
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← hQ y', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [show y' * (k : GR n) * (k1 * a * k2) = y' * (k : GR n) * (k1 * a) * k2 by group,
      ((hM n p q e).1 _ k2 hk2).1]
    field_simp
  have hkey := key _ (W.smul_mem _ hQW) hQ'
  have hIk2 : ∀ k : KR n, I 1 (gpt * ι ((k : GR n) * (k1 * a * k2))) =
      F0 p q e k2 * I 1 (gpt * ι ((k : GR n) * (k1 * a))) := by
    intro k
    rw [show (k : GR n) * (k1 * a * k2) = (k : GR n) * (k1 * a) * k2 by group, map_mul, ← mul_assoc,
      hG.Ik 1 _ k2 hk2, hL.kvac k2 hk2, map_smul, Pi.smul_apply, smul_eq_mul]
  calc ∫ k, κ k * I 1 (gpt * ι ((k : GR n) * (k1 * a * k2))) ∂ν
      = ∫ k, F0 p q e k2 * (κ k * I 1 (gpt * ι ((k : GR n) * (k1 * a)))) ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only; rw [hIk2 k]; ring
    _ = F0 p q e k2 * I ((F0 p q e k2)⁻¹ • Q) gpt := by rw [integral_const_mul, hkey]
    _ = I Q gpt := by
        rw [map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hF2, one_mul]

end PositivityTheory.Rg.Sw.AbsSt

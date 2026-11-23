import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLSliceSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLSliceDZ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLine
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

namespace SSPw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def conjL (A : Wp →L[ℂ] Wp) (B : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) where
  toFun X := A.comp (X.comp B)
  map_add' X Y := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c X := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl

def sumL {ι : Type} [Fintype ι] (f : ι → (Wq →L[ℂ] Wp)) (V : ι → (Wq →L[ℂ] Wp)) :
    (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ ρ, (((innerₛₗ ℂ (B.hsVec (f ρ))).comp Formalism.FourierDecayAlt.P.JFxI.hsVecL).smulRight (V ρ))

theorem sumL_apply {ι : Type} [Fintype ι] (f : ι → (Wq →L[ℂ] Wp)) (V : ι → (Wq →L[ℂ] Wp)) (Y : Wq →L[ℂ] Wp) :
    sumL f V Y = ∑ ρ, inner ℂ (B.hsVec (f ρ)) (B.hsVec Y) • V ρ := by
  unfold sumL
  rw [LinearMap.sum_apply]
  rfl

end SSPw

open SSPw in
theorem second_shift_pointwise_holds : SSn.Rep.Core.SSPointwise := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl
  obtain ⟨hpl, hL, hS, hRel, hQQ⟩ := hA
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl

  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set μ0 := TheSec.theSection P.k P.r Bs.z Bs.z' with hμ0
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hcs0.1 }
  have hyp0 : Gauge.GC.GTHyp P Bs0 X d := ⟨hpl, hk, hcs0, hL, hS, hRel, hQQ⟩
  obtain ⟨e0, he0, -⟩ := Gauge.GC.gauge_kappa_holds Wp Wq P Bs0 X d hyp0

  have hRT := Gauge.GC.radial_torus_local_holds Wp Wq P Bs0 hpl hk hcs0 X
  have hSl : ∀ (Y : ℂ) (a b : Fin 2), Gauge.GC.SliceLoc P Bs0 (X.t Y a b) := fun Y a b =>
    Gauge.GC.second_shift_slice_derivative Wp Wq P Bs0 hpl _ (hRT Y a b)
  have hSL := (Gauge.GC.second_shift_slice_operator Wp Wq P Bs0 X d hyp0 hSl l hl).1

  have hC : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute (d.SS l).1 W := by
    intro f hf W hW
    obtain ⟨W₁, hW₁⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZ f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZ_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    obtain ⟨W₂, hW₂⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZb f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZb_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    exact ((Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl X d hL hS hRel hQQ f hf W W₁ W₂
      hW hW₁ hW₂).2.1 l hl).1

  have hRB0 : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := Gauge.GC.radBase_of P Bs0 hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he0.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB0 _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs0.μsec ζ) = e0 ρ ζ := by
    intro ρ c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have h := congrFun (hΨr ρ) (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h

  have hdec : ∀ ζ : ℂ, ∃ hh : Q.Mx P.k P.r × Q.Mx P.k P.r, ζ ∈ Gauge.GC.Ann P →
      hh.1 ∈ UWset P.k P.r Bs.z ∧ hh.2 ∈ UWset P.k P.r Bs.z' ∧
        NF.muZ P.k P.r Bs.μsec ζ = hh.1 * NF.muZ P.k P.r μ0 ζ * hh.2 := by
    intro ζ
    by_cases hζ : ζ ∈ Gauge.GC.Ann P
    · have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ⟩
      have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
      obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hcs0.1
        hdom.2.1 hdom.2.2
      rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hq.2] at he
      exact ⟨(h, h'), fun _ => ⟨hh, hh', he⟩⟩
    · exact ⟨(1, 1), fun h => absurd h hζ⟩
  choose H hH using hdec
  let V : M.Ty P → ℂ → (Wq →L[ℂ] Wp) := fun ρ ζ =>
    ((d.SS l).1 (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r μ0 ζ)
  refine ⟨fun ζ => LinearMap.toContinuousLinearMap
    ((conjL (Bs.π (H ζ).1) (Bs.π' (H ζ).2)) ∘ₗ sumL (fun ρ => e0 ρ ζ) (fun ρ => V ρ ζ) ∘ₗ
      conjL (Bs.π (H ζ).1⁻¹) (Bs.π' (H ζ).2⁻¹)), ?_⟩
  intro Φ c hc ζ hζ
  obtain ⟨hh, hh', hd⟩ := hH ζ hζ
  set h := (H ζ).1
  set h' := (H ζ).2
  have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hdom0 := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs0.1 hq
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'

  have hback : NF.muZ P.k P.r μ0 ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
    rw [hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
      Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
  have hΦ0 : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r μ0 ζ) =
      (Bs.π h⁻¹).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)) := by
    rw [hback]
    exact Φ.2.2.2 (c, NF.muZ P.k P.r Bs.μsec ζ) hdom h⁻¹ hhi h'⁻¹ hhi'

  have hfwd : (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r Bs.μsec ζ) =
      (Bs.π h).comp (((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r μ0 ζ)).comp (Bs.π' h')) := by
    rw [hd]
    exact ((d.SS l).1 Φ).2.2.2 (c, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh'
  have hkey := Gauge.GC.key_slice P Bs0 hpl hk e0 he0 Ψ hΨ (d.SS l).1 hSL hC Φ hc hc0 hζ
  rw [hfwd]
  change _ = (Bs.π h).comp ((sumL (fun ρ => e0 ρ ζ) (fun ρ => V ρ ζ)
    ((Bs.π h⁻¹).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)))).comp
      (Bs.π' h'))
  rw [← hΦ0, sumL_apply]
  congr 2

end

end Formalism.FourierDecayAlt.P.CutMP.JA

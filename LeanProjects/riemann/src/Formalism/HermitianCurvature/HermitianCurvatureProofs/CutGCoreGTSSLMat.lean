import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocalCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem wRc_smooth (P : M.Par) : ContDiffOn ℝ ∞ (fun ζ : ℂ => ((wR P.k P.TT ζ : ℝ) : ℂ)) (Ann P) := by
  have h1 : ContDiffOn ℝ ∞ (fun ζ : ℂ => (Complex.normSq ζ - P.TT) ^ (P.k - 1)) (Ann P) := by
    have h2 : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
      have h3 : (fun ζ : ℂ => Complex.normSq ζ) = fun ζ : ℂ => ‖ζ‖ ^ 2 := by
        funext ζ
        rw [Complex.normSq_eq_norm_sq]
      rw [h3]
      exact contDiff_norm_sq ℝ
    exact ((h2.sub contDiff_const).pow _).contDiffOn
  have h4 : ContDiffOn ℝ ∞ (fun ζ : ℂ => wR P.k P.TT ζ) (Ann P) := by
    unfold wR
    refine h1.sqrt fun ζ hζ => ?_
    have h5 : P.TT < Complex.normSq ζ := hζ
    exact (pow_pos (by linarith) _).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h4

theorem wRc_ne (P : M.Par) {ζ : ℂ} (hζ : ζ ∈ Ann P) : ((wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by
  have h5 : P.TT < Complex.normSq ζ := hζ
  have h6 : 0 < wR P.k P.TT ζ := by
    unfold wR
    exact Real.sqrt_pos.mpr (pow_pos (by linarith) _)
  exact_mod_cast h6.ne'

section mat

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tz_TT (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem radBase_of (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
  exact ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, Bs.sec, Bs.π_rep, Bs.π'_rep, Bs.π_cont,
    Bs.π'_cont⟩

theorem slice_smooth (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r) :
    ContDiffOn ℝ ∞ (fun ζ => inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))) (Ann P) := by
  have hm : ContDiffOn ℝ ∞ (MA.ext (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)) (MA.Qset P.r P.TT) :=
    radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have h1 : ContDiffOn ℝ ∞ (fun ζ : ℂ => MA.ext (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) (c, ζ))
      (Ann P) :=
    hm.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun ζ hζ => ⟨hc, hζ⟩)
  refine (Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_div h1 (wRc_smooth P) fun ζ hζ => wRc_ne P hζ).congr fun ζ hζ => ?_
  have hq : ((c, ζ) : MA.E P.r) ∈ MA.Qset P.r P.TT := ⟨hc, hζ⟩
  simp only [MA.ext, dif_pos hq, rawR]
  rw [mul_div_cancel_left₀ _ (wRc_ne P hζ)]

theorem key_slice (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hT : SliceLoc P Bs T)
    (hC : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute T W)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') {c c0 : Fin P.r → ℂ} (hc : c ∈ OmX P.r) (hc0 : c0 ∈ OmX P.r)
    {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) •
        (T (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) := by
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  let F : M.Ty P → ℂ → ℂ := fun ρ ζ' => inner ℂ (B.hsVec (e ρ ζ'))
    (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ')))
  have hFs : ∀ ρ, ContDiffOn ℝ ∞ (F ρ) {ζ | P.TT < Complex.normSq ζ} := fun ρ =>
    slice_smooth P Bs hpl hk e he Φ ρ hc
  choose W hW using fun ρ => Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (F ρ) (hFs ρ)
  have hQR : ∀ c' ∈ OmX P.r, ∀ ζ' ∈ Ann P, ((c', ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
    fun c' hc' ζ' hζ' => ⟨hc', by rw [hTz]; exact hζ'⟩
  have hmul : ∀ (ρ : M.Ty P) (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ c' ∈ OmX P.r, ∀ ζ' ∈ Ann P,
      ((W ρ Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ') =
        F ρ ζ' • (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ') := by
    intro ρ Θ c' hc' ζ' hζ'
    have hq := hQR c' hc' ζ' hζ'
    rw [hW ρ Θ]
    have h := Formalism.FourierDecayAlt.P.NFRO.radR_mulZ hRB (F ρ) Θ.2 hq
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  let Φc : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ∑ ρ, W ρ (Ψ ρ)
  have hsumv : ∀ (G : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c' : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      ((∑ ρ, G ρ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' g =
        ∑ ρ, (G ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' g := by
    intro G c' g
    rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  have hΦv : ∀ ζ' ∈ Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ') =
      (Φc : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ') := by
    intro ζ' hζ'
    have hq := hQR c hc ζ' hζ'
    rw [hsumv]
    have hmem := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2).2.1 (c, ζ') hq
    simp only [NF.radR, Set.indicator_of_mem hq] at hmem
    rw [(he.2 ζ' hζ').2.2 _ hmem]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hmul ρ (Ψ ρ) c hc ζ' hζ', hΨ ρ c hc ζ' hζ']
  rw [hT Φ Φc c c hc hc hΦv ζ hζ, map_sum, hsumv]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hcomm : T (W ρ (Ψ ρ)) = W ρ (T (Ψ ρ)) := by
    have h := (hC (F ρ) (hFs ρ) (W ρ) (hW ρ)).eq
    exact LinearMap.congr_fun h (Ψ ρ)
  rw [hcomm, hmul ρ (T (Ψ ρ)) c hc ζ hζ]
  congr 1
  exact hT (Ψ ρ) (Ψ ρ) c c0 hc hc0 (fun ζ' hζ' => by rw [hΨ ρ c hc ζ' hζ', hΨ ρ c0 hc0 ζ' hζ']) ζ hζ

end mat

theorem second_shift_matrix_form : GTSSLMat := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hSL
  obtain ⟨hpl, hk, -, hL, hS, hRel, hQQ⟩ := hH
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ := by
    intro ρ c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have h := congrFun (hΨr ρ) (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  have hCom : ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f →
        Commute (d.SS l).1 W ∧ Commute (star (d.SS l)).1 W := by
    intro l hl f hf W hW
    obtain ⟨W₁, hW₁⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZ f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZ_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    obtain ⟨W₂, hW₂⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZb f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZb_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    exact (Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl X d hL hS hRel hQQ f hf W W₁ W₂
      hW hW₁ hW₂).2.1 l hl
  let ent : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') → M.Ty P → M.Ty P → ℂ → ℂ := fun T ρ' ρ ζ =>
    inner ℂ (B.hsVec (e ρ' ζ)) (B.hsVec ((T (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)))
  have hent : ∀ T ρ' ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ent T ρ' ρ) (Ann P) := fun T ρ' ρ =>
    slice_smooth P Bs hpl hk e he (T (Ψ ρ)) ρ' hc0
  have hmain : ∀ (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), SliceLoc P Bs T →
      (∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
        ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute T W) →
      ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P),
        trR P Bs e (T Φ) ρ' = ∑ ρ, fnZ P (ent T ρ' ρ) * trR P Bs e Φ ρ := by
    intro T hT hC Φ ρ'
    have hv : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P),
        ((trR P Bs e Θ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
          rawR P Bs.μsec e (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ := fun Θ σ =>
      Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem P (radial_space_smoothness Wp Wq P Bs hpl hk e he Θ σ)
    apply Subtype.ext
    funext q
    rw [hv]
    rw [show (((∑ ρ, fnZ P (ent T ρ' ρ) * trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) =
        ∑ ρ, ent T ρ' ρ q.1.2 * rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q by
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [MulMemClass.coe_mul, Pi.mul_apply, hv, fnZ_eq_mk P (hent T ρ' ρ)]]
    have hc : q.1.1 ∈ OmX P.r := q.2.1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    simp only [rawR]
    rw [key_slice P Bs hpl hk e he Ψ hΨ T hT hC Φ hc hc0 hζ, Formalism.FourierDecayAlt.P.CutMP.En.hsVec_sum_smul, inner_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [inner_smul_right]
    ring
  refine ⟨fun l => ent (d.SS l).1, fun l => ent (star (d.SS l)).1,
    fun l ρ' ρ => ⟨hent _ ρ' ρ, hent _ ρ' ρ⟩, ?_⟩
  intro l hl Φ ρ'
  exact ⟨hmain _ (hSL l hl).1 (fun f hf W hW => (hCom l hl f hf W hW).1) Φ ρ',
    hmain _ (hSL l hl).2 (fun f hf W hW => (hCom l hl f hf W hW).2) Φ ρ'⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

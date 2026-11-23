import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSIo

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

namespace Tr

section datum

variable {k r : ℕ}

theorem unitH_uh {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.unitH k r (h *ᵥ v) = h *ᵥ SSn.unitH k r v := by
  unfold SSn.unitH
  rw [Formalism.FourierDecayAlt.P.Qx2.herm_uh hh, Matrix.mulVec_smul]

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μ μ0 : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {ζ : ℂ} {h h' : B.Mat k r}

theorem section_first_vector_transport (hz : inWb k r z) (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (hd : NF.muZ k r μ ζ = h * NF.muZ k r μ0 ζ * h') :
    SSn.nu0 k r z z' μ ζ = h *ᵥ SSn.nu0 k r z z' μ0 ζ := by
  unfold SSn.nu0
  rw [hd, ← Matrix.mulVec_mulVec, hh'.2.2, ← Matrix.mulVec_mulVec, kap_prWv_mulVec hz hh, unitH_uh hh.1]

theorem nu0'_tr (hz' : inWb k r z') (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (hd : NF.muZ k r μ ζ = h * NF.muZ k r μ0 ζ * h') :
    SSn.nu0' k r z z' μ ζ = h'⁻¹ *ᵥ SSn.nu0' k r z z' μ0 ζ := by
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
  unfold SSn.nu0'
  rw [hd, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hhi.2.2,
    kap_prWv_mulVec hz' hhi', unitH_uh hhi'.1]

theorem section_embedding_transport (hz' : inWb k r z') (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (hd : NF.muZ k r μ ζ = h * NF.muZ k r μ0 ζ * h') :
    SSn.io0 k r z z' μ ζ = h * SSn.io0 k r z z' μ0 ζ * h' := by
  apply Formalism.FourierDecayAlt.P.Qx8.mat_ext
  intro v
  set ν := SSn.nu0' k r z z' μ0 ζ with hν
  have e1 : h' *ᵥ (h'⁻¹ *ᵥ ν) = ν := by
    rw [Matrix.mulVec_mulVec, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.one_mulVec]
  have e2 : ∀ w, herm (Hpk k r) (h' *ᵥ w) ν = herm (Hpk k r) w (h'⁻¹ *ᵥ ν) := by
    intro w
    conv_lhs => rw [← e1]
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hh'.1 _ _
  rw [MC.DT.ioMulVec, nu0'_tr hz' hh hh' hd, ← hν, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, MC.DT.ioMulVec, ← hν,
    kap_prWv_mulVec hz' hh', e2, hd, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul, e1]

end datum

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem rep_inv_l {π : B.Mat k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (y : Wp) : π h⁻¹ (π h y) = y := by
  have e : (π h⁻¹).comp (π h) = 1 := by
    rw [← hπ.2 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh) _ hh, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, hπ.1]
  exact congrArg (fun T : Wp →L[ℂ] Wp => T y) e

theorem rep_inv_r {π : B.Mat k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (y : Wp) : π h (π h⁻¹ y) = y := by
  have e : (π h).comp (π h⁻¹) = 1 := by
    rw [← hπ.2 _ hh _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh), Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, hπ.1]
  exact congrArg (fun T : Wp →L[ℂ] Wp => T y) e

end ops

section fib

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μ μ0 : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {ζ : ℂ}
  {h h' : B.Mat k r} {π : B.Mat k r → (Wp →L[ℂ] Wp)} {π' : B.Mat k r → (Wq →L[ℂ] Wq)}

theorem fib_tr (hπ : IsCRepOn (UWset k r z) π) (hπ' : IsCRepOn (UWset k r z') π')
    (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (hd : NF.muZ k r μ ζ = h * NF.muZ k r μ0 ζ * h') {Xf : Wq →L[ℂ] Wp} (hX : Xf ∈ NF.Fib k r z z' μ π π' ζ) :
    (π h⁻¹).comp (Xf.comp (π' h'⁻¹)) ∈ NF.Fib k r z z' μ0 π π' ζ := by
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hst : (h * p.1 * h⁻¹, h'⁻¹ * p.2 * h') ∈ NF.Stab k r z z' μ ζ := by
    refine ⟨Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) hhi,
      Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) hh', ?_⟩
    show h * p.1 * h⁻¹ * NF.muZ k r μ ζ * (h'⁻¹ * p.2 * h') = NF.muZ k r μ ζ
    rw [hd]
    calc h * p.1 * h⁻¹ * (h * NF.muZ k r μ0 ζ * h') * (h'⁻¹ * p.2 * h')
        = h * p.1 * (h⁻¹ * h) * NF.muZ k r μ0 ζ * (h' * h'⁻¹) * p.2 * h' := by simp only [Matrix.mul_assoc]
      _ = h * (p.1 * NF.muZ k r μ0 ζ * p.2) * h' := by
          rw [Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh']
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = h * NF.muZ k r μ0 ζ * h' := by rw [hp3]
  have hfix := hX _ hst
  apply ContinuousLinearMap.ext
  intro x
  have h1 := congrArg (fun T : Wq →L[ℂ] Wp => T (π' h'⁻¹ x)) hfix
  simp only [ContinuousLinearMap.comp_apply] at h1
  rw [hπ.2 _ (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) _ hhi, hπ.2 _ hh _ hp1,
    hπ'.2 _ (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) _ hh', hπ'.2 _ hhi' _ hp2] at h1
  simp only [ContinuousLinearMap.comp_apply] at h1
  rw [rep_inv_r hπ' hh'] at h1
  simp only [ContinuousLinearMap.comp_apply]
  rw [← h1, rep_inv_l hπ hh]

end fib

end Tr

open Tr in
theorem transfer_holds : Transfer := by
  intro hTF h0 Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp
  have hpl := hA.1
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set μ0 := TheSec.theSection P.k P.r Bs.z Bs.z' with hμ0
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hcs0.1 }
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero

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
  let S0 : ℂ → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun ζ =>
    (sandw (Bs.π (H ζ).1⁻¹) (Bs.π' (H ζ).2⁻¹)).comp ((S ζ).comp (sandw (Bs.π (H ζ).1) (Bs.π' (H ζ).2)))
  have hS0 : IsSSPt P Bs0 d l S0 := by
    intro Φ c hc ζ hζ
    obtain ⟨hh, hh', hd⟩ := hH ζ hζ
    set h := (H ζ).1 with hh_def
    set h' := (H ζ).2 with hh'_def
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
    have hdom0 := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs0.1 hq
    have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
    have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
    have hback : NF.muZ P.k P.r μ0 ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
      rw [hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
        Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
    have hb1 : (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
          (NF.muZ P.k P.r μ0 ζ) =
        (Bs.π h⁻¹).comp (((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
          (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)) := by
      rw [hback]
      exact ((d.SS l).1 Φ).2.2.2 (c, NF.muZ P.k P.r Bs.μsec ζ) hdom h⁻¹ hhi h'⁻¹ hhi'
    have hf : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
        (Bs.π h).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r μ0 ζ)).comp (Bs.π' h')) := by
      rw [hd]
      exact Φ.2.2.2 (c, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh'
    change (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
          (NF.muZ P.k P.r μ0 ζ) =
      (Bs.π h⁻¹).comp ((S ζ ((Bs.π h).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r μ0 ζ)).comp
        (Bs.π' h')))).comp (Bs.π' h'⁻¹))
    rw [← hf, ← hS Φ c hc ζ hζ]
    exact hb1
  obtain ⟨n, q, hq⟩ := h0 Wp Wq P Bs0 rfl hk X d hA l hl S0 hS0 Pr hPr Bw Bw' hBw hBw' π ρ hUp
  refine ⟨n, q, fun ζ hζ Xf hXf hline => ?_⟩
  obtain ⟨hh, hh', hd⟩ := hH ζ hζ
  set h := (H ζ).1 with hh_def
  set h' := (H ζ).2 with hh'_def
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
  have hinv : h'⁻¹⁻¹ = h' := Matrix.nonsing_inv_nonsing_inv h' (WeylGroupFacts.isUnit_of_uh hh'.1)
  have eν := section_first_vector_transport (z' := Bs.z') hz hh hh' hd
  have eν' := nu0'_tr (z := Bs.z) hz' hh hh' hd
  have eι := section_embedding_transport (z := Bs.z) hz' hh hh' hd
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' μ0 ζ with hν
  set ν' := SSn.nu0' P.k P.r Bs.z Bs.z' μ0 ζ with hν'
  set ι := SSn.io0 P.k P.r Bs.z Bs.z' μ0 ζ with hι
  set Xf0 : Wq →L[ℂ] Wp := (Bs.π h⁻¹).comp (Xf.comp (Bs.π' h'⁻¹)) with hXf0
  have hXb : (Bs.π h).comp (Xf0.comp (Bs.π' h')) = Xf := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [hXf0, ContinuousLinearMap.comp_apply]
    rw [rep_inv_l Bs.π'_rep hh', rep_inv_r Bs.π_rep hh]
  have hmem0 : Xf0 ∈ NF.Fib P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' ζ := fib_tr Bs.π_rep Bs.π'_rep hh hh' hd hXf
  have hPrT : ∀ σ : M.Ty P, Pr σ (h *ᵥ ν) = (Bs.π h).comp ((Pr σ ν).comp (Bs.π h⁻¹)) := fun σ => hPr.2.1 h hh σ ν
  have hline0 : (Pr π ν).comp Xf0 = Xf0 := by
    rw [eν, hPrT] at hline
    apply ContinuousLinearMap.ext
    intro x
    have h1 := congrArg (fun T : Wq →L[ℂ] Wp => Bs.π h⁻¹ (T (Bs.π' h'⁻¹ x))) hline
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [rep_inv_l Bs.π_rep hh] at h1
    simp only [hXf0, ContinuousLinearMap.comp_apply]
    exact h1
  have hkey : (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ ν).comp (S0 ζ Xf0) =
      q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) • (Pr ρ ν).comp
        (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' ν ν' ι Xf0) := hq ζ hζ Xf0 hmem0 hline0
  have hS0v : S0 ζ Xf0 = (Bs.π h⁻¹).comp ((S ζ Xf).comp (Bs.π' h'⁻¹)) := by
    change (Bs.π h⁻¹).comp ((S ζ ((Bs.π h).comp (Xf0.comp (Bs.π' h')))).comp (Bs.π' h'⁻¹)) = _
    rw [hXb]
  have hT := ((hTF Wp Wq P Bs hpl Bw Bw' hBw hBw').2.2.2.1 h hh h'⁻¹ hhi' ν ν' ι Xf0).1
  rw [hinv, hXb] at hT
  rw [eν, eν', eι, hT, hPrT]
  rw [hS0v] at hkey
  apply ContinuousLinearMap.ext
  intro x
  have h1 := congrArg (fun T : Wq →L[ℂ] Wp => Bs.π h (T (Bs.π' h' x))) hkey
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul] at h1
  rw [rep_inv_l Bs.π'_rep hh'] at h1
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply]
  rw [rep_inv_l Bs.π_rep hh]
  exact h1

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPhaseCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTransfer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLine
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

theorem rot_normSq (θ : ℝ) (ζ : ℂ) : Complex.normSq (rot θ ζ) = Complex.normSq ζ := by
  unfold rot
  rw [map_mul, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  simp

open Tr in
theorem phase_invariance_of_truncation : PhaseInvOfCut := by
  intro hPS hT21 hRR hTR hK hA hD hF Wp Wq _ _ _ _ _ _ P Bs hsec hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hUp θ
  have hAct' := hAct
  obtain ⟨hpl, hL, hSt, hRel, hQQ⟩ := hAct'
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hTT : 0 < P.TT := by rw [← hTz]; exact mul_pos Bs.T_pos Bs.T'_pos
  have hcs := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  rw [← hsec] at hcs
  have hAnn : ∀ ζ ∈ Gauge.GC.Ann P, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ :=
    fun ζ hζ => by rw [hTz]; exact hζ
  obtain ⟨ζ₁, hζ₁⟩ : ∃ ζ₁ : ℂ, ζ₁ ∈ Gauge.GC.Ann P := by
    refine ⟨((P.TT + 1 : ℝ) : ℂ), ?_⟩
    show P.TT < Complex.normSq ((P.TT + 1 : ℝ) : ℂ)
    rw [Complex.normSq_ofReal]; nlinarith
  have hrotA : ∀ ζ ∈ Gauge.GC.Ann P, rot θ ζ ∈ Gauge.GC.Ann P := by
    intro ζ hζ
    show P.TT < Complex.normSq (rot θ ζ)
    rw [rot_normSq]; exact hζ
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁ := ⟨_, rfl⟩
  obtain ⟨ν', hν'def⟩ : ∃ ν', ν' = SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ₁ := ⟨_, rfl⟩
  obtain ⟨ι, hιdef⟩ : ∃ ι, ι = SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ₁ := ⟨_, rfl⟩
  have hDc : ∀ ζ ∈ Gauge.GC.Ann P,
      SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = ν ∧ SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ = ν' ∧
      SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = ι := by
    intro ζ hζ
    rw [hνdef, hν'def, hιdef, hsec]
    exact hD P.k P.r Bs.z Bs.z' (by omega) Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos ζ ζ₁ (hAnn ζ hζ) (hAnn ζ₁ hζ₁)
  have hFc : ∀ ζ ∈ Gauge.GC.Ann P,
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := by
    intro ζ hζ
    unfold NF.Fib
    rw [hcs.2 ζ ζ₁ (hAnn ζ hζ) (hAnn ζ₁ hζ₁)]
  obtain ⟨Qr, hKP, hKL⟩ := hK Wp Wq P Bs hsec hk X d hAct Pr hPr
  have hKL1 : ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁, ∀ σ : M.Ty P,
      (Pr σ ν).comp Xf = Xf.comp (Qr σ) := by
    intro Xf hXf σ
    rw [hνdef]
    exact hKL ζ₁ hζ₁ Xf hXf σ
  have hGT : Gauge.GC.GTHyp P Bs X d := ⟨hpl, hk, hcs, hL, hSt, hRel, hQQ⟩
  have hLine := Gauge.GC.gauge_kappa_line_holds Wp Wq P Bs X d hGT Qr hKP ζ₁ hζ₁
  obtain ⟨Eπ, hEπF, hEπQ, hEπn, hEπsp⟩ := hLine π
  obtain ⟨Eρ, hEρF, hEρQ, hEρn, hEρsp⟩ := hLine ρ
  have hQQr : ∀ σ, (Qr σ).comp (Qr σ) = Qr σ := fun σ => by rw [hKP.1 σ σ, if_pos rfl]
  have hdomZ : ∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
      ((c, NF.muZ P.k P.r Bs.μsec ζ) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈ Q.DomR P.k P.r Bs.z Bs.z' := by
    intro c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, hAnn ζ hζ⟩
    exact Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec hq

  have hval : ∀ (Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r →
      ∀ ζ ∈ Gauge.GC.Ann P, (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := by
    intro Ψ c hc ζ hζ
    rw [← hFc ζ hζ]
    intro p hp
    have h1 := Ψ.2.2.2 (c, NF.muZ P.k P.r Bs.μsec ζ) (hdomZ c hc ζ hζ) p.1 hp.1 p.2 hp.2.1
    simp only at h1
    rw [hp.2.2] at h1
    exact h1.symm
  have hEρne : Eρ ≠ 0 := by
    intro h0
    rw [h0] at hEρn
    have : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := (Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq)).map_zero
    rw [this, inner_zero_left] at hEρn
    exact zero_ne_one hEρn
  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := Gauge.GC.radBase_of P Bs hpl

  have hmk : ∀ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁, ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = E := by
    intro E hE
    have hsecE : ((NF.QR P.k P.r Bs.z Bs.z').indicator fun _ : (Fin P.r → ℂ) × ℂ => E) ∈
        NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
      refine ⟨(contDiffOn_const (c := E)).congr fun q hq => by simp [Set.indicator_of_mem hq], fun q hq => ?_,
        fun q hq => by simp [Set.indicator_of_notMem hq]⟩
      rw [Set.indicator_of_mem hq, hFc q.2 (by show P.TT < _; rw [← hTz]; exact hq.2)]
      exact hE
    obtain ⟨Φ0, hΦ0, hΦr⟩ :=
      Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ hsecE
    refine ⟨⟨Φ0, hΦ0⟩, fun c hc ζ hζ => ?_⟩
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, hAnn ζ hζ⟩
    have h := congrFun hΦr (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero

  obtain ⟨h, h', hh, hh', hsecθ, hh'W⟩ :=
    hPS P.k P.r Bs.z Bs.z' (by omega) Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos θ
  simp only [CP.mu0] at hsecθ
  rw [← hsec] at hsecθ
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
  have hμrot : ∀ ζ ∈ Gauge.GC.Ann P, NF.muZ P.k P.r Bs.μsec (rot θ ζ) =
      h * cW P.k P.r θ * NF.muZ P.k P.r Bs.μsec ζ * h' := fun ζ hζ => (hsecθ ζ (hAnn ζ hζ)).2.2
  have hback : ∀ ζ ∈ Gauge.GC.Ann P, cW P.k P.r θ * NF.muZ P.k P.r Bs.μsec ζ =
      h⁻¹ * NF.muZ P.k P.r Bs.μsec (rot θ ζ) * h'⁻¹ := by
    intro ζ hζ
    rw [hμrot ζ hζ]
    calc cW P.k P.r θ * NF.muZ P.k P.r Bs.μsec ζ
        = (h⁻¹ * h) * (cW P.k P.r θ * NF.muZ P.k P.r Bs.μsec ζ) * (h' * h'⁻¹) := by
          rw [Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.one_mul, Matrix.mul_one]
      _ = h⁻¹ * (h * cW P.k P.r θ * NF.muZ P.k P.r Bs.μsec ζ * h') * h'⁻¹ := by simp only [Matrix.mul_assoc]
  have hdomC : ∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
      ((c, cW P.k P.r θ * NF.muZ P.k P.r Bs.μsec ζ) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈
        Q.DomR P.k P.r Bs.z Bs.z' := by
    intro c hc ζ hζ
    rw [hback ζ hζ]
    exact Formalism.FourierDecayAlt.P.Qx5.DomR_inv hhi hhi' (hdomZ c hc _ (hrotA ζ hζ))
  obtain ⟨A, hAdef⟩ : ∃ A, A = sandw (Bs.π h) (Bs.π' h') := ⟨_, rfl⟩
  obtain ⟨Ai, hAidef⟩ : ∃ Ai, Ai = sandw (Bs.π h⁻¹) (Bs.π' h'⁻¹) := ⟨_, rfl⟩
  have hAap : ∀ Z : Wq →L[ℂ] Wp, A Z = (Bs.π h).comp (Z.comp (Bs.π' h')) := fun Z => by rw [hAdef]; rfl
  have hAiap : ∀ Z : Wq →L[ℂ] Wp, Ai Z = (Bs.π h⁻¹).comp (Z.comp (Bs.π' h'⁻¹)) := fun Z => by rw [hAidef]; rfl
  have hAAi : ∀ Z : Wq →L[ℂ] Wp, A (Ai Z) = Z := by
    intro Z
    rw [hAap, hAiap]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    rw [rep_inv_l Bs.π'_rep hh', rep_inv_r Bs.π_rep hh]
  have hAiA : ∀ Z : Wq →L[ℂ] Wp, Ai (A Z) = Z := by
    intro Z
    rw [hAap, hAiap]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    rw [rep_inv_r Bs.π'_rep hh', rep_inv_l Bs.π_rep hh]

  have hνh : h *ᵥ ν = Complex.exp (-((θ : ℂ) * Complex.I)) • ν := by
    rw [hνdef]; exact (hsecθ ζ₁ (hAnn ζ₁ hζ₁)).1
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    obtain ⟨hνfix, hνν, -, -⟩ := DU.base Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec (hAnn ζ₁ hζ₁)
    unfold PRho.nrmW
    rw [hνdef, hνfix, hνν]; simp
  have hPc : ∀ (σ : M.Ty P) (y : Wp), Pr σ ν (Bs.π h⁻¹ y) = Bs.π h⁻¹ (Pr σ ν y) := by
    intro σ y
    have h1 := hPr.2.1 h hh σ ν
    rw [hνh, (hPr.2.2 ν hpos).1 σ _ (Complex.exp_ne_zero _)] at h1
    have h2 := congrArg (fun T : Wp →L[ℂ] Wp => Bs.π h⁻¹ (T y)) h1
    simp only [ContinuousLinearMap.comp_apply] at h2
    rw [rep_inv_l Bs.π_rep hh] at h2
    exact h2.symm
  have hPAi : ∀ (σ : M.Ty P) (Z : Wq →L[ℂ] Wp), (Pr σ ν).comp (Ai Z) = Ai ((Pr σ ν).comp Z) := by
    intro σ Z
    rw [hAiap, hAiap]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    exact hPc σ _

  have hF4 : ∀ (Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r → ∀ ζ ∈ Gauge.GC.Ann P,
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (cW P.k P.r θ * NF.muZ P.k P.r Bs.μsec ζ) =
        Ai ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec (rot θ ζ))) := by
    intro Ψ c hc ζ hζ
    rw [hback ζ hζ, hAiap]
    exact Ψ.2.2.2 (c, NF.muZ P.k P.r Bs.μsec (rot θ ζ)) (hdomZ c hc _ (hrotA ζ hζ)) h⁻¹ hhi h'⁻¹ hhi'
  let Rθ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun Ψ =>
    ⟨fun c g => (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (cW P.k P.r θ * g),
      hRR Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bs.z_mem Bs.z'_mem θ Ψ.1 Ψ.2⟩
  have hRθ : ∀ (Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r → ∀ ζ ∈ Gauge.GC.Ann P,
      (Rθ Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
        Ai ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec (rot θ ζ))) := hF4

  have hlineAi : ∀ σ : M.Ty P, ∀ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁, E.comp (Qr σ) = E →
      Ai E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ ∧ (Ai E).comp (Qr σ) = Ai E := by
    intro σ E hE hEQ
    obtain ⟨Φ, hΦ⟩ := hmk E hE
    have h1 : Ai E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := by
      have h2 := hval (Rθ Φ) c0 hc0 ζ₁ hζ₁
      rw [hRθ Φ c0 hc0 ζ₁ hζ₁, hΦ c0 hc0 _ (hrotA ζ₁ hζ₁)] at h2
      exact h2
    refine ⟨h1, ?_⟩
    rw [← hKL1 _ h1 σ, hPAi, hKL1 E hE σ, hEQ]
  obtain ⟨aπ, hAiπ⟩ : ∃ aπ : ℂ, Ai Eπ = aπ • Eπ :=
    ⟨_, hEπsp _ (hlineAi π Eπ hEπF hEπQ).1 (hlineAi π Eπ hEπF hEπQ).2⟩
  obtain ⟨aρ, hAiρ⟩ : ∃ aρ : ℂ, Ai Eρ = aρ • Eρ :=
    ⟨_, hEρsp _ (hlineAi ρ Eρ hEρF hEρQ).1 (hlineAi ρ Eρ hEρF hEρQ).2⟩
  have haρ : aρ ≠ 0 := by
    intro h0
    apply hEρne
    rw [← hAAi Eρ, hAiρ, h0, zero_smul, map_zero]

  have hAiρ' : ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁, Z.comp (Qr ρ) = Z → Ai Z = aρ • Z := by
    intro Z hZ hZQ
    rw [hEρsp Z hZ hZQ, map_smul, hAiρ, smul_comm]
  obtain ⟨Φ, hΦ⟩ := hmk Eπ hEπF
  have hsum : ∀ σ : M.Ty P, (∑ τ, (Pi.single σ (1 : ℂ) : M.Ty P → ℂ) τ • Qr τ) = Qr σ := by
    intro σ
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [hτ]) (fun h => absurd (Finset.mem_univ σ) h)]
    simp
  have hKπ : (d.κ (Pi.single π 1)).1 Φ = Φ := by
    apply Subtype.ext
    refine Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _
      ((d.κ (Pi.single π 1)).1 Φ).2 _ Φ.2 (funext fun q => ?_)
    by_cases hq : q ∈ NF.QR P.k P.r Bs.z Bs.z'
    · simp only [NF.radR, Set.indicator_of_mem hq]
      have hqA : q.2 ∈ Gauge.GC.Ann P := by show P.TT < _; rw [← hTz]; exact hq.2
      have h1 := hKP.2.2.2 (Pi.single π 1) Φ ⟨(q.1, q.2), hq.1, hqA⟩
      simp only at h1
      rw [h1, hsum, hΦ q.1 hq.1 q.2 hqA, hEπQ]
    · simp only [NF.radR, Set.indicator_of_notMem hq]
  have hΦθ : Rθ Φ = aπ • Φ := by
    apply Subtype.ext
    refine Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _
      (Rθ Φ).2 _ (aπ • Φ).2 (funext fun q => ?_)
    by_cases hq : q ∈ NF.QR P.k P.r Bs.z Bs.z'
    · simp only [NF.radR, Set.indicator_of_mem hq]
      have hqA : q.2 ∈ Gauge.GC.Ann P := by show P.TT < _; rw [← hTz]; exact hq.2
      rw [hRθ Φ q.1 hq.1 q.2 hqA, hΦ q.1 hq.1 _ (hrotA q.2 hqA), hAiπ, Submodule.coe_smul]
      simp only [Pi.smul_apply]
      rw [hΦ q.1 hq.1 q.2 hqA]
    · simp only [NF.radR, Set.indicator_of_notMem hq]

  obtain ⟨Y, hY⟩ : ∃ Y : ℂ, M.xEx P {l} π Y ≠ 0 := by
    refine ⟨((1 + ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i| : ℝ) : ℂ), ?_⟩
    unfold M.xEx
    rw [Finset.prod_ne_zero_iff]
    intro i hi h0
    have h2 := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h2
    have hle : |M.rho P π i| ≤ ∑ j ∈ Finset.Icc 1 (P.k - 1), |M.rho P π j| :=
      Finset.single_le_sum (f := fun j => |M.rho P π j|) (fun j _ => abs_nonneg _) (Finset.mem_sdiff.1 hi).1
    linarith [neg_abs_le (M.rho P π i)]

  have hAlg := hA P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) d hRel l hl π ρ hUp Y
  have hAlg1 : (d.κ (Pi.single ρ 1)).1 (X.t Y 1 0 Φ) = M.xEx P {l} π Y • (d.SS l).1 Φ := by
    have h := congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 Φ) hAlg
    rw [← hQQ Y] at h
    change ((d.κ (Pi.single ρ 1)).1 * (X.t Y 1 0) * (d.κ (Pi.single π 1)).1) Φ =
      (algebraMap ℂ (Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (M.xEx P {l} π Y) *
        ((d.SS l).1 * (d.κ (Pi.single π 1)).1)) Φ at h
    simp only [Module.End.mul_apply, Module.algebraMap_end_apply] at h
    rw [hKπ] at h
    exact h
  obtain ⟨T, hTdef⟩ : ∃ T : ℂ → (Wq →L[ℂ] Wp), ∀ ζ, T ζ =
      (X.t Y 1 0 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) := ⟨_, fun _ => rfl⟩
  have hTF : ∀ ζ ∈ Gauge.GC.Ann P, T ζ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := by
    intro ζ hζ
    rw [hTdef]
    exact hval _ c0 hc0 ζ hζ
  have hPt : ∀ ζ ∈ Gauge.GC.Ann P, M.xEx P {l} π Y • S ζ Eπ = (T ζ).comp (Qr ρ) := by
    intro ζ hζ
    have e1 := congrArg (fun Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' =>
      (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)) hAlg1
    have h1 := hKP.2.2.2 (Pi.single ρ 1) (X.t Y 1 0 Φ) ⟨(c0, ζ), hc0, hζ⟩
    simp only at h1 e1
    rw [h1, hsum, Submodule.coe_smul] at e1
    simp only [Pi.smul_apply] at e1
    rw [hS Φ c0 hc0 ζ hζ, hΦ c0 hc0 ζ hζ, ← hTdef] at e1
    exact e1.symm
  have hS2 : ∀ ζ ∈ Gauge.GC.Ann P, S ζ Eπ = (M.xEx P {l} π Y)⁻¹ • (T ζ).comp (Qr ρ) := by
    intro ζ hζ
    rw [← hPt ζ hζ, smul_smul, inv_mul_cancel₀ hY, one_smul]
  have hSF : ∀ ζ ∈ Gauge.GC.Ann P, S ζ Eπ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := by
    intro ζ hζ
    have h := hval ((d.SS l).1 Φ) c0 hc0 ζ hζ
    rw [hS Φ c0 hc0 ζ hζ, hΦ c0 hc0 ζ hζ] at h
    exact h
  have hSQ : ∀ ζ ∈ Gauge.GC.Ann P, (S ζ Eπ).comp (Qr ρ) = S ζ Eπ := by
    intro ζ hζ
    rw [hS2 ζ hζ, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, hQQr]

  have hTrot : ∀ ζ ∈ Gauge.GC.Ann P,
      Ai (T (rot θ ζ)) = (Complex.exp (-((θ : ℂ) * Complex.I)) * aπ) • T ζ := by
    intro ζ hζ
    have h1 := X.t_apply Y 1 0 Φ (c0, cW P.k P.r θ * NF.muZ P.k P.r Bs.μsec ζ) (hdomC c0 hc0 ζ hζ)
    have h2 := X.t_apply Y 1 0 (Rθ Φ) (c0, NF.muZ P.k P.r Bs.μsec ζ) (hdomZ c0 hc0 ζ hζ)
    have h3 := hT21 P.k P.r Bs.z Bs.z' Bs.z_mem (Wq →L[ℂ] Wp) θ Y ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0)
      (NF.muZ P.k P.r Bs.μsec ζ) (hdomZ c0 hc0 ζ hζ).2.1
    simp only at h1 h2
    change _ = Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0
      (fun x => (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (cW P.k P.r θ * x)) (NF.muZ P.k P.r Bs.μsec ζ) at h2
    rw [hTdef, ← hF4 (X.t Y 1 0 Φ) c0 hc0 ζ hζ, h1, h3, ← h2, hΦθ, map_smul, Submodule.coe_smul]
    simp only [Pi.smul_apply]
    rw [smul_smul, ← hTdef]
  have hmain : ∀ ζ ∈ Gauge.GC.Ann P,
      Ai (S (rot θ ζ) Eπ) = (Complex.exp (-((θ : ℂ) * Complex.I)) * aπ) • S ζ Eπ := by
    intro ζ hζ
    rw [hS2 _ (hrotA ζ hζ), hS2 ζ hζ, map_smul, ← hKL1 _ (hTF _ (hrotA ζ hζ)) ρ, ← hPAi, hTrot ζ hζ,
      ContinuousLinearMap.comp_smul, hKL1 _ (hTF ζ hζ) ρ, smul_comm]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = aρ⁻¹ * (Complex.exp (-((θ : ℂ) * Complex.I)) * aπ) := ⟨_, rfl⟩
  have hfin1 : ∀ ζ ∈ Gauge.GC.Ann P, S (rot θ ζ) Eπ = c • S ζ Eπ := by
    intro ζ hζ
    have h1 := hmain ζ hζ
    rw [hAiρ' _ (hSF _ (hrotA ζ hζ)) (hSQ _ (hrotA ζ hζ))] at h1
    rw [hcdef, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ haρ, one_smul]

  obtain ⟨Th, hThdef⟩ : ∃ Th, Th = tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' ν ν' ι := ⟨_, rfl⟩
  have hTh : A (Th (Ai Eπ)) = Complex.exp ((θ : ℂ) * Complex.I) • Th (A (Ai Eπ)) := by
    rw [hAap, hAap, hThdef, hνdef, hν'def, hιdef]
    exact hTR Wp Wq P Bs hpl hk hsec Bw Bw' hBw hBw' θ h h' hh hh' ζ₁ hζ₁ (hsecθ ζ₁ (hAnn ζ₁ hζ₁)).1
      (hsecθ ζ₁ (hAnn ζ₁ hζ₁)).2.1 hh'W (Ai Eπ)
  obtain ⟨R, hRdef⟩ : ∃ R, R = (Pr ρ ν).comp (Th Eπ) := ⟨_, rfl⟩
  have hThF : Th Eπ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := by
    rw [hThdef, hνdef, hν'def, hιdef]
    exact (hF Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' ζ₁ hζ₁ Eπ hEπF ρ).2
  have hRF : R ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₁ := by
    rw [hRdef, hνdef]
    exact (hF Wp Wq P Bs hpl hk Pr hPr Bw Bw' hBw hBw' ζ₁ hζ₁ _ hThF ρ).1
  have hRQ : R.comp (Qr ρ) = R := by
    rw [hRdef, hKL1 _ hThF ρ, ContinuousLinearMap.comp_assoc, hQQr]
  have hR1 : aπ • R = (Complex.exp ((θ : ℂ) * Complex.I) * aρ) • R := by
    rw [hAAi, hAiπ, map_smul, map_smul] at hTh
    have h1 := congrArg (fun Z => (Pr ρ ν).comp (Ai Z)) hTh
    simp only [map_smul, hAiA] at h1
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul, hPAi, ← hRdef, hAiρ' R hRF hRQ, smul_smul] at h1
    exact h1
  have hfin2 : R = c • R := by
    have he : Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [hcdef, ← mul_assoc, mul_smul, hR1, smul_smul]
    have : aρ⁻¹ * Complex.exp (-((θ : ℂ) * Complex.I)) * (Complex.exp ((θ : ℂ) * Complex.I) * aρ) = 1 := by
      calc aρ⁻¹ * Complex.exp (-((θ : ℂ) * Complex.I)) * (Complex.exp ((θ : ℂ) * Complex.I) * aρ)
          = (Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I)) * (aρ⁻¹ * aρ) := by ring
        _ = 1 := by rw [he, inv_mul_cancel₀ haρ, one_mul]
    rw [this, one_smul]
  refine ⟨c, fun ζ hζ Xf hXf hXl => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hDc ζ hζ
  obtain ⟨f1, f2, f3⟩ := hDc _ (hrotA ζ hζ)
  rw [f1, f2, f3, e1, e2, e3, ← hThdef]
  rw [e1] at hXl
  rw [hFc ζ hζ] at hXf
  rw [hKL1 Xf hXf π] at hXl
  obtain ⟨x, hx⟩ : ∃ x : ℂ, Xf = x • Eπ := ⟨_, hEπsp Xf hXf hXl⟩
  subst hx
  refine ⟨?_, ?_⟩
  · rw [map_smul, map_smul, hfin1 ζ hζ, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_smul, smul_comm]
  · rw [map_smul, ContinuousLinearMap.comp_smul, ← hRdef, smul_comm, ← hfin2]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

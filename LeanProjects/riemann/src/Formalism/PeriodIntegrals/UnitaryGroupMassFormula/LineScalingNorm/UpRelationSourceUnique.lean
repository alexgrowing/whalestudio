import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.ConstantOneMemNonvanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLEig

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

noncomputable section

theorem up_relation_source_unique {P : M.Par} {l : ℕ} {a b c : M.Ty P} (h1 : M.Up P l a b) (h2 : M.Up P l c b) : a = c := by
  funext i
  apply Fin.ext
  have e1 := h1 i
  have e2 := h2 i
  omega

theorem up_tgt {P : M.Par} {l : ℕ} {a b c : M.Ty P} (h1 : M.Up P l a b) (h2 : M.Up P l a c) : b = c := by
  funext i
  apply Fin.ext
  have e1 := h1 i
  have e2 := h2 i
  omega

section line

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem line_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) (σ : M.Ty P) (ζ : ℂ) (c : ℂ)
    {E : Wq →L[ℂ] Wp} (hE : E ∈ Line P Bs Pr σ ζ) : c • E ∈ Line P Bs Pr σ ζ := by
  refine ⟨fun p hp => ?_, ?_⟩
  · rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hE.1 p hp]
  · rw [ContinuousLinearMap.comp_smul, hE.2]

theorem lineQ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hH : Gauge.GC.GTHyp P Bs X d)
    (Qs : M.Ty P → (Wq →L[ℂ] Wq)) (hQ : Gauge.GC.KapPt P Bs d Qs)
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) (hPr : PRho.PRhoSpec P Bs.z Bs.π Pr)
    (ζ : ℂ) (hζ : ζ ∈ Gauge.GC.Ann P) (σ : M.Ty P) (E : Wq →L[ℂ] Wp)
    (hE : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ) :
    E ∈ Line P Bs Pr σ ζ ↔ E.comp (Qs σ) = E := by
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hH.1
  have hk : 2 ≤ P.k := hH.2.1
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp

  have pass : ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z, ν] Fr →
      Q.IsFrameOf P.k P.r [μ⁻¹ *ᵥ Bs.z, Bs.z'] (fun a => μ⁻¹ *ᵥ Fr a) ∧
      ∀ (w : ℂ) (v : Wq), Q.capRep P.k P.r Bs.π Fr w (E v) =
        E (qdet (Qr.EB Bs.π' (fun a => μ⁻¹ *ᵥ Fr a)) w v) := by
    intro Fr hFr
    obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
    have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
      (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
      (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
    refine ⟨hFr', fun w v => ?_⟩
    rw [hpass E hE, hgl']
  constructor
  · intro hL
    obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
    obtain ⟨hFr', hp⟩ := pass Fr hFr
    have hcap : Gauge.GC.CapEig P Bs.π' (fun a => μ⁻¹ *ᵥ Fr a) σ E := by
      intro Yc v
      have hEv : Pr σ ν (E v) = E v := by
        have := DFunLike.congr_fun hL.2 v
        simpa only [ContinuousLinearMap.comp_apply] using this
      have hr := ((hPr.2.2 ν hpos).2.2.2 σ (E v)).1 hEv Fr (by rw [hνfix]; exact hFr)
        (Yc + ((P.k : ℂ) - 2) / 2)
      rw [hp] at hr
      have e : Yc + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Yc := by ring
      rw [e] at hr
      exact hr
    exact (Gauge.GC.lie_eigenvalue_holds Wp Wq P Bs X d hH Qs hQ ζ hζT _ hFr' σ E hE).2 hcap
  · intro hEQ
    refine ⟨hE, ?_⟩
    ext v
    show Pr σ ν (E v) = E v
    refine ((hPr.2.2 ν hpos).2.2.2 σ (E v)).2 fun Fr hFr w => ?_
    rw [hνfix] at hFr
    obtain ⟨hFr', hp⟩ := pass Fr hFr
    have hcap := (Gauge.GC.lie_eigenvalue_holds Wp Wq P Bs X d hH Qs hQ ζ hζT _ hFr' σ E hE).1 hEQ
    have h1 := hcap (w - ((P.k : ℂ) - 2) / 2) v
    rw [sub_add_cancel] at h1
    rw [hp, h1]

end line

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

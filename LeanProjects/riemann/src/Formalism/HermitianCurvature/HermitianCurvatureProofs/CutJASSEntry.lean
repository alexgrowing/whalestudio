import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

namespace SSEn

theorem coe_sum_apply {r : ℕ} {TT : ℝ} {ι : Type} (s : Finset ι) (g : ι → MA.SmQ r TT) (q : MA.Qp r TT) :
    Subtype.val (∑ i ∈ s, g i) q = ∑ i ∈ s, Subtype.val (g i) q := by
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

theorem ss_entry_apply (P : M.Par) (l : ℕ) (ρ π' : M.Ty P) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 f) q =
      (if M.Up P l π' ρ then ((Real.sqrt (M.Nrm P l π') : ℝ) : ℂ) else 0) * (f : MA.Qp P.r P.TT → ℂ) q := by
  simp only [MA.SS, Matrix.of_apply]
  split_ifs with h
  · rfl
  · rw [zero_mul]
    rfl

end SSEn

open SSEn in
theorem second_shift_entry_holds : SSn.Rep.Core.SSEntry := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hSSF l hl S hS ζ hζ π ρ
  obtain ⟨hpl, hL, hSt, hRel, hQQ⟩ := hA
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hRB := Gauge.GC.radBase_of P Bs hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero

  have hsec : ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e π q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨((he.1 π).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 π
    · simp [Set.indicator_of_notMem hq]
  obtain ⟨Ψ0, hΨ0, hΨr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ hsec
  let Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Ψ0, hΨ0⟩
  have hΨ : (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) = e π ζ := by
    have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ⟩
    have h := congrFun hΨr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h

  have hv : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P),
      ((Gauge.GC.trR P Bs e Θ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
        Gauge.rawR P Bs.μsec e (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ := fun Θ σ =>
    Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem P (Gauge.GC.radial_space_smoothness Wp Wq P Bs hpl hk e he Θ σ)
  let q : MA.Qp P.r P.TT := ⟨((c0, ζ) : MA.E P.r), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hw := Gauge.GC.wRc_ne P hζ

  have e1 : Subtype.val (Gauge.GC.trR P Bs e ((d.SS l).1 Ψ) ρ) q =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) := by
    refine (congrFun (hv ((d.SS l).1 Ψ) ρ) q).trans ?_
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec ((((d.SS l).1 Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0
        (NF.muZ P.k P.r Bs.μsec ζ))) = _
    rw [hS Ψ c0 hc0 ζ hζ, hΨ]

  have e2 : Subtype.val (Gauge.GC.trR P Bs e ((d.SS l).1 Ψ) ρ) q =
      ∑ π', Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 (Gauge.GC.trR P Bs e Ψ π')) q := by
    refine (congrArg (fun F : M.Ty P → MA.SmQ P.r P.TT => Subtype.val (F ρ) q) (hSSF l hl Ψ).1).trans ?_
    exact coe_sum_apply _ _ _
  have hterm : ∀ π' : M.Ty P, Subtype.val (Gauge.GC.trR P Bs e Ψ π') q =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (if π' = π then 1 else 0) := by
    intro π'
    rw [congrFun (hv Ψ π') q]
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e π' ζ))
      (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ))) = _
    rw [hΨ, (he.2 ζ hζ).2.1 π' π]
  have e3 : ∑ π', Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 (Gauge.GC.trR P Bs e Ψ π')) q =
      (if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0) * ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) := by
    simp only [ss_entry_apply, hterm]
    rw [Finset.sum_eq_single π (fun π' _ hne => by simp [hne]) (fun h => absurd (Finset.mem_univ π) h)]
    simp
  have h2 : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) *
        (if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0) := by
    rw [← e1, e2, e3, mul_comm]
  exact mul_left_cancel₀ hw h2

end

end Formalism.FourierDecayAlt.P.CutMP.JA

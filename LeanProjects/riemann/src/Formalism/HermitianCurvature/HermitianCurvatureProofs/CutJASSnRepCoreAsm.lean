import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core

noncomputable section

theorem theta_gauge_constancy_holds : ThtGaugeConstOfCore := by
  intro hA hPt hTh hE hPR hGL hDU
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ v e hH hk l hl Bw Bw' hBw hBw'
  obtain ⟨hB, hFr, hGa, hQQ⟩ := hH
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v)
    (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' hPl
  obtain ⟨d, hd1, hd2, hd3, hd4⟩ := Formalism.FourierDecayAlt.P.normal_form_actual (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v)
    (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' hPl X
  have hAct : ActHyp (D.parOf S v) (T v).base X d := ⟨hPl, hd1, hd2, hd3, hd4⟩
  obtain ⟨SS, hSS⟩ := hPt (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct l hl
  obtain ⟨Pr, hPr⟩ := hPR (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk
  obtain ⟨θ, hθ⟩ := hTh (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct l hl SS hSS Pr hPr
    Bw Bw' hBw hBw'
  have hFrB : Gauge.IsFrameB (D.parOf S v) (T v).base e := hFr
  have hGQ : GQQ (D.parOf S v) (T v).base e := hQQ
  have hSSF := hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct e hFrB hGQ
  refine ⟨θ, fun ζ hζ π ρ hup => ?_⟩
  have hent := hE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct e hFrB hSSF l hl SS hSS ζ hζ π ρ
  rw [if_pos hup] at hent
  obtain ⟨hP1, hH1, -, -⟩ := hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v ζ hζ
  set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ with hn0
  have hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1 := by
    unfold PRho.nrmW; rw [hP1, hH1]; simp
  obtain ⟨-, -, hrest⟩ := hPr
  have hpos : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z n0 := by rw [hN0]; norm_num

  have hfix : ∀ τ y, Pr τ n0 (e τ ζ y) = e τ ζ y := by
    intro τ y
    refine ((hrest n0 hpos).2.2.2 τ (e τ ζ y)).2 ?_
    intro Fr hFrm w
    rw [hP1] at hFrm
    exact hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk ζ hζ τ Fr hFrm w y
  have hfixc : ∀ τ, (Pr τ n0).comp (e τ ζ) = e τ ζ := fun τ => by ext y; exact hfix τ y
  have hsa := (hrest n0 hpos).2.1 ρ
  have hfib : e π ζ ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' ζ :=
    ((hFrB.2 ζ hζ).1 π)
  set B0 : Wq (S.pl v) →L[ℂ] Wp (S.pl v) := tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    Bw Bw' n0 (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
    (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) (e π ζ) with hB0
  have key : (Pr ρ n0).comp (SS ζ (e π ζ)) = θ π • (Pr ρ n0).comp B0 :=
    hθ ζ hζ π ρ hup (e π ζ) hfib (hfixc π)

  have hmove : ∀ Y : Wq (S.pl v) →L[ℂ] Wp (S.pl v),
      inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp Y)) = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Y) := by
    intro Y
    have h1 := hsInner_lmul (Pr ρ n0) hsa Y (e ρ ζ)
    simp only [B.hsInner, lmul_apply] at h1
    rw [hfixc ρ] at h1
    exact h1
  have hsm : ∀ (c : ℂ) (A : Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A
    unfold B.hsVec
    ext i
    simp
  calc θ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec B0)
      = θ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp B0)) := by rw [hmove]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (θ π • (Pr ρ n0).comp B0)) := by rw [hsm, inner_smul_right]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp (SS ζ (e π ζ)))) := by rw [key]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (SS ζ (e π ζ))) := hmove _
    _ = _ := hent

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core

import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ChiLawAmbOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VacEntire
import Formalism.PeriodIntegrals.VacEntire
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section An

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eNat_analytic (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hθ : AnalyticOnNhd ℂ B.thMM Set.univ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AnalyticOnNhd ℂ (B.eNat χ N N' L L') Set.univ := by
  have hT := entireStatements_holds
  have h0 : AnalyticOnNhd ℂ (B.thZero N N') Set.univ := hT.2 _ B.thMM N N' hθ
  have h1 : AnalyticOnNhd ℂ (B.thHalf N N' L) Set.univ := hT.1 _ _ _ _ _ _ _ _ h0
  have h2 : AnalyticOnNhd ℂ (B.thMoved N N' L L') Set.univ := hT.1 _ _ _ _ _ _ _ _ h1
  intro z _
  exact analyticAt_const.mul (h2 z (Set.mem_univ _))

variable {X : Fields} (s : Seam D X) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem eOmega_ambOf {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) (a b : ℕ) : (ambOf s B χ cD : Amb X).EOmega a b := by
  obtain ⟨hcc, hδ, -, -, -, -, -⟩ := hN
  intro N N' _ _
  have hA := eNat_analytic B χ (Formalism.L2.KerInert.AlgP.thMM_analytic B (B.stdOK hcc hδ)) a b (s.lat N) (s.lat N')
  have hc : ContDiff ℂ ⊤ (B.eNat χ a b (s.lat N) (s.lat N')) := hA.contDiff
  exact hc.comp (contDiff_pi.2 fun τ => contDiff_apply ℂ _ (s.iT.symm τ))

end An

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem thEquivP_ambOf {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ)
    (he : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩)
    (hrat : (ambOf s B χ cD : Amb X).JetsRat (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (hInd : (ambOf s B χ cD : Amb X).ThIndEq (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (hMa : MuProdLaw (R.N i) sel (rowSG Pr sel mu) (mUof Ch mu i) (muAtT Ch sel mu cst i) e)
    (hMb : MuProdLaw (R.N (i + 1)) sel (rowSG Pr sel mu) (mUof Ch mu i) (muAtT Ch sel mu cst i) e) :
    ThEquivP (stepT W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho :=
  thEquivP_stepT_of W Ch sel mu cst (ambOf s B χ cD) u hi e he hrat (eOmega_ambOf s B χ cD hN _ _) hInd
    (chiLaw_ambOf s B χ cD hN (even_rankN R i) (even_rankN R (i + 1))) hMa hMb

end Main

end Formalism.L2.Ker

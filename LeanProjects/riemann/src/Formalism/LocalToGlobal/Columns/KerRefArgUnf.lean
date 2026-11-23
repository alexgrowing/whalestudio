import Formalism.LocalToGlobal.Columns.XiHypOfThHyp
import Formalism.LocalToGlobal.Columns.FixEColLevSym

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (Am : Amb X) (u : Pr.Word) (m2 : ℕ)

abbrev symIdxD : ChIdx X Pr R (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) :=
  oneIdx (colLevSym Ch) (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2

abbrev symXi : XiFam Pr R u :=
  refXi1 Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) (exceptional_primes_trivial_tuple sel S) m2 (oneAl (colLevSym Ch) sel (mu0 X.F X.E X.K S) m2) u

structure KerRefHyp {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (Gc : ChGlob X R.m) : Prop where
  hX : X.Ok
  hPr : Pr.Ok
  hm : R.m = m2 + 2
  sig : Am.σ₀ = σ₀
  thHyp : ThHyp W Ch sel (mu0 X.F X.E X.K S) cst Am u m2
  stepTop : Am.StepHyp (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) (Sall sel (mu0 X.F X.E X.K S) u)
    (cAof sel (mu0 X.F X.E X.K S) cst * cBof sel (mu0 X.F X.E X.K S) cst u)
  lawTop : ThEquivP (stepT W Ch sel (mu0 X.F X.E X.K S) cst Am u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel (mu0 X.F X.E X.K S) u)
    (cAof sel (mu0 X.F X.E X.K S) cst * cBof sel (mu0 X.F X.E X.K S) cst u)
    (colValF W sel (mu0 X.F X.E X.K S) u (m2 + 1)).rho (colValF W sel (mu0 X.F X.E X.K S) u (m2 + 1 + 1)).rho
  idx : (symIdxD Ch sel S m2).Ok Ch sel (mu0 X.F X.E X.K S) cst Gc m2
  xiLaw : ∀ i, i < m2 → ∀ (al : (symIdxD Ch sel S m2).β i) (be : (symIdxD Ch sel S m2).β (i + 1)),
    XiLaw Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) i al be
  psiLaw : ∀ al, PsiLaw Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) m2 al (oneAl (colLevSym Ch) sel (mu0 X.F X.E X.K S) m2 (m2 + 1) le_rfl)
  topLaw : TopLawG Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) m2 (colLevSym Ch (m2 + 1 + 1))
    (oneAl (colLevSym Ch) sel (mu0 X.F X.E X.K S) m2 (m2 + 1) le_rfl)
  chi_ne : ∀ i, i < R.m → ∀ (c : StCl W (colLevSym Ch) u i) (c' : StCl W (colLevSym Ch) u (i + 1)),
    Am.chiF (R.N i) (R.N (i + 1)) (repN W (colLevSym Ch) u i c) (repN W (colLevSym Ch) u (i + 1) c') ≠ 0
  rho : RhoScal W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst G Am u

variable {W Ch sel S cst Am u m2}

theorem KerRefHyp.xiEquiv {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {Gc : ChGlob X R.m} (H : KerRefHyp W Ch sel S cst Am u m2 G Gc) :
    XiEquiv W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst Am u (symXi Ch sel S cst u m2) :=
  kernelEquiv_trivialTuple W (colLevSym Ch) Ch sel S cst Am u m2 H.hX H.hPr (by have := H.hm; omega) H.thHyp H.idx H.xiLaw H.psiLaw (fixE_colLevSym Ch H.hm)
    (refKEquiv_of_cpTop H.hX H.hPr (fixE_colLevSym Ch H.hm) (coupling_index_set_finite sel _ cst _ u m2 _)
      (cpTopEquivOn_of H.hX H.hPr H.idx.cst_ok (exceptional_primes_trivial_tuple sel S) (topNum_of H.hm) _
        (chTh_thTop_ok W Ch sel _ cst Am u m2 (by have := H.hm; omega) (H.hPr.T_prime u).pos (muqTie_of_allG Ch sel _ cst (bad_primes_over_g_trivial_tuple sel S)) H.stepTop H.lawTop)
        _ _ _ _ H.topLaw (lastRow_colLevSym Ch H.hm)))

theorem KerRefHyp.xiHyp {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {Gc : ChGlob X R.m} (H : KerRefHyp W Ch sel S cst Am u m2 G Gc) :
    XiHyp W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst Am u (symXi Ch sel S cst u m2) G :=
  xiHyp_of_thHyp H.hm H.sig H.hPr H.thHyp H.chi_ne H.rho

def kerRefArg {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {Gc : ChGlob X R.m} (H : KerRefHyp W Ch sel S cst Am u m2 G Gc) :
    ChainArg W (colLevSym Ch) G u :=
  refArg1 W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) (exceptional_primes_trivial_tuple sel S) m2 (oneAl (colLevSym Ch) sel (mu0 X.F X.E X.K S) m2) Am u
    H.hm H.xiEquiv H.xiHyp

end Fin

end Formalism.L2.Col

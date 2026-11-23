import Formalism.LocalToGlobal.Columns.KerRefArgUnf
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThHypDeg

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section XiD

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word) (Ξ : XiFam Pr R u)

structure XiHypD {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) : Prop where
  sig : Am.σ₀ = σ₀
  T_pos : 0 < Pr.T u
  smooth : ∀ i, i < R.m → Am.ESmooth (R.N i) (R.N (i + 1))
  rat : ∀ i, i < R.m → Am.JetsRatDeg (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i)
  chi_ne : ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
    Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') ≠ 0
  rho : RhoScal W Λ Ch sel mu cst G Am u
  above : ∀ i, R.m ≤ i → ∀ p p' x, Ξ i p p' x = 0

variable {W Λ Ch sel mu cst Am u Ξ}

theorem xiTheta_tieD {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (hE : XiEquiv W Λ Ch sel mu cst Am u Ξ) (H : XiHypD W Λ Ch sel mu cst Am u Ξ G) :
    (xiTheta W Λ sel mu cst Am u Ξ).Comparison₂ G (xiKK hE) := by
  intro i c c' x
  by_cases hi : i < R.m
  · have hp := ((stepGSD W Λ u i).outSec.rep c).2
    have hp' := ((stepGSD W Λ u (i + 1)).outSec.rep c').2
    have h := unfTh_stepCD W Ch sel mu cst Am σ₀ H.sig u H.T_pos hi (jet_in_weight_space_chain W u hi) (H.smooth i hi) (H.rat i hi)
      (repN W Λ u i c) (repFr W Λ sel mu u i c) (repN W Λ u (i + 1) c') (repFr W Λ sel mu u (i + 1) c')
      ⟨hp.lat, hp.uni⟩ ⟨hp'.lat, hp'.uni⟩
      (Ξ i ((stepGSD W Λ u i).outSec.rep c) ((stepGSD W Λ u (i + 1)).outSec.rep c')) x
    have hr := H.rho i hi c c'
    have hx := H.chi_ne i hi c c'
    set r := σ₀ (rhoK W Λ G.chr u i c : X.K) * σ₀ (rhoK' W Λ G.chr u i c' : X.K) with hrdef
    have h0 : r ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · intro h; have := rhoK_norm G u i c; rw [h, norm_zero] at this; exact zero_ne_one this
      · intro h; have := rhoK'_norm G u i c'; rw [h, norm_zero] at this; exact zero_ne_one this
    have hs : σ₀ (scalK Ch sel mu cst i (repN W Λ u i c) (repFr W Λ sel mu u i c) (repN W Λ u (i + 1) c') (repFr W Λ sel mu u (i + 1) c')) *
        (Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c'))⁻¹ = r := by
      rw [← hr, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    rw [hs] at h
    funext (y' : FrS X σ₀ (R.N (i + 1)))
    have hy := congrFun h y'
    refine Eq.trans ?_ (congrArg (fun z : ℂ => r⁻¹ * z) hy).symm
    show _ = r⁻¹ * (r * _)
    rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    rfl
  · have hi' : R.m ≤ i := Nat.le_of_not_lt hi
    have hk : (xiKK hE i).k ((stepGSD W Λ u i).outSec.rep c) ((stepGSD W Λ u (i + 1)).outSec.rep c') = 0 :=
      kerOf_zero _ _ _ _ _ _ _ _ _ (H.above i hi' _ _)
    have ht : (xiTheta W Λ sel mu cst Am u Ξ).Th i c c' = fun _ => 0 := thDat_zero Am _ _ _ _ _ _ (H.above i hi' _ _)
    rw [hk, ht, unfTh_zero]
    simp
    rfl

def ChainArg.ofXiD {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} (hE : XiEquiv W Λ Ch sel mu cst Am u Ξ) (H : XiHypD W Λ Ch sel mu cst Am u Ξ G) :
    ChainArg W Λ G u :=
  ChainArg.ofTheta (xiKK hE) (xiTheta W Λ sel mu cst Am u Ξ) (xiTheta_tieD G hE H)

end XiD

section FinD

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (Am : Amb X) (u : Pr.Word) (m2 : ℕ)

structure KerRefHypD {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (Gc : ChGlob X R.m) : Prop where
  hX : X.Ok
  hPr : Pr.Ok
  hm : R.m = m2 + 2
  sig : Am.σ₀ = σ₀
  thHyp : ThHypD W Ch sel (mu0 X.F X.E X.K S) cst Am u m2
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

theorem KerRefHypD.xiEquiv {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {Gc : ChGlob X R.m} (H : KerRefHypD W Ch sel S cst Am u m2 G Gc) :
    XiEquiv W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst Am u (symXi Ch sel S cst u m2) :=
  xiEquiv_one H.hX H.hPr (fixE_colLevSym Ch H.hm)
    (matEquiv_mu0D W Ch sel S cst _ Am u m2 (by have := H.hm; omega) H.hPr H.thHyp H.idx H.xiLaw) (coupling_index_set_finite sel _ cst _ u m2 _)
    (cp1EquivOn_mu0D W Ch sel S cst _ Am u m2 (by have := H.hm; omega) H.hPr H.thHyp H.idx _ _ H.psiLaw)
    (refKEquiv_of_cpTop H.hX H.hPr (fixE_colLevSym Ch H.hm) (coupling_index_set_finite sel _ cst _ u m2 _)
      (cpTopEquivOn_of H.hX H.hPr H.idx.cst_ok (exceptional_primes_trivial_tuple sel S) (topNum_of H.hm) _
        (chTh_thTop_okD W Ch sel _ cst Am u m2 (by have := H.hm; omega) (H.hPr.T_prime u).pos (muqTie_of_allG Ch sel _ cst (bad_primes_over_g_trivial_tuple sel S))
          (anaStepD_of_thHypD W Ch sel _ cst Am u m2 H.hm H.thHyp (m2 + 1) (by have := H.hm; omega)) H.lawTop)
        _ _ _ _ H.topLaw (lastRow_colLevSym Ch H.hm)))

theorem KerRefHypD.xiHyp {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {Gc : ChGlob X R.m} (H : KerRefHypD W Ch sel S cst Am u m2 G Gc) :
    XiHypD W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst Am u (symXi Ch sel S cst u m2) G where
  sig := H.sig
  T_pos := (H.hPr.T_prime u).pos
  smooth := fun i hi => (anaStepD_of_thHypD W Ch sel _ cst Am u m2 H.hm H.thHyp i hi).2.1
  rat := fun i hi => (anaStepD_of_thHypD W Ch sel _ cst Am u m2 H.hm H.thHyp i hi).2.2
  chi_ne := H.chi_ne
  rho := H.rho
  above := fun i hi p p' x => refXi1_above Ch sel _ cst _ (exceptional_primes_trivial_tuple sel S) m2 _ u H.hm i hi p p' x

def kerRefArgD {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {Gc : ChGlob X R.m} (H : KerRefHypD W Ch sel S cst Am u m2 G Gc) :
    ChainArg W (colLevSym Ch) G u :=
  ChainArg.ofXiD H.xiEquiv H.xiHyp

end FinD

end Formalism.L2.Col

import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RatKDeg
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete
import Formalism.LocalToGlobal.Columns.RecChainUnfOne

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Mu0

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (L : ChIdx X Pr R (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem chTh_ok_mu0D (hm : m2 + 1 < R.m) (hPr : Pr.Ok) (hTh : ThHypD W Ch sel (mu0 X.F X.E X.K S) cst A u m2) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel (mu0 X.F X.E X.K S) cst A u m2) :=
  chTh_ok_ambD W Ch sel _ cst A u m2 hm (hPr.T_prime u).pos (muqTie_of_allG Ch sel _ cst (bad_primes_over_g_trivial_tuple sel S)) hTh

theorem matEquiv_mu0D (hm : m2 + 1 < R.m) (hPr : Pr.Ok) (hTh : ThHypD W Ch sel (mu0 X.F X.E X.K S) cst A u m2) {G : ChGlob X R.m}
    (hL : L.Ok Ch sel (mu0 X.F X.E X.K S) cst G m2)
    (hX : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)), XiLaw Ch sel (mu0 X.F X.E X.K S) cst L i al be) :
    MatEquiv W Ch sel (mu0 X.F X.E X.K S) cst L (chTh W Ch sel (mu0 X.F X.E X.K S) cst A u m2) :=
  matEquiv_of W Ch sel _ cst L A u m2 (exceptional_primes_trivial_tuple sel S) (hPr.T_prime u).pos (chTh_ok_mu0D W Ch sel S cst A u m2 hm hPr hTh)
    (fun i hi al be p p' x z hz => xiEntry_inv Ch sel _ cst L (exceptional_primes_trivial_tuple sel S) hPr hL i hi al be p p' x z hz) hX

theorem cp1EquivOn_mu0D (hm : m2 + 1 < R.m) (hPr : Pr.Ok) (hTh : ThHypD W Ch sel (mu0 X.F X.E X.K S) cst A u m2) {G : ChGlob X R.m}
    (hL : L.Ok Ch sel (mu0 X.F X.E X.K S) cst G m2) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel (mu0 X.F X.E X.K S) cst L u m2 b)
    (hPsi : ∀ al : L.β m2, PsiLaw Ch sel (mu0 X.F X.E X.K S) cst L m2 al b) :
    Cp1EquivOn W Ch sel (mu0 X.F X.E X.K S) cst L (chTh W Ch sel (mu0 X.F X.E X.K S) cst A u m2) b hY :=
  cp1EquivOn_of W Ch sel _ cst L A u m2 (exceptional_primes_trivial_tuple sel S) (hPr.T_prime u).pos hPr (chTh_ok_mu0D W Ch sel S cst A u m2 hm hPr hTh) hL b hY hPsi

end Mu0

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem chTh_thTop_okD (A : Amb X) (u : Pr.Word) (m2 : ℕ) (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst)
    (hs : A.AnaStepD (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u (m2 + 1)))
    (heqT : ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colValF W sel mu u (m2 + 1 + 1)).rho) :
    ThDist.Ok ((chTh W Ch sel mu cst A u m2).th (m2 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (colValF W sel mu u (m2 + 1)).rho
      (colValF W sel mu u (m2 + 1 + 1)).rho (rhoS Ch sel mu (m2 + 1)) (rhoT Ch sel mu (m2 + 1)) :=
  stepC_ok_deg W Ch sel mu cst A u (m2 + 1) hm _ hT _ _ hq hs heqT

theorem anaStepD_of_thHypD (A : Amb X) (u : Pr.Word) (m2 : ℕ) (hm : R.m = m2 + 2) (hTh : ThHypD W Ch sel mu cst A u m2) (i : ℕ) (hi : i < R.m) :
    A.AnaStepD (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i) := by
  rcases Nat.lt_or_ge m2 i with h | h
  · have e : i = m2 + 1 := by omega
    subst e
    have h2 := hTh.2.1
    rw [hm] at h2
    exact h2
  · exact hTh.1 i h

end Top

end Formalism.L2.Ker

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker MvPolynomial Matrix Module

section Ev

variable {X : Fields} {a b : ℕ}

theorem unfTh_evD (σ₀ : X.K →+* ℂ) (cD : X.Tau → ℂ) (Θ : VCx X.Tau a b → ℂ) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b)
    (n : X.Tau → ℕ) (s' s : X.Tau → ℤ) (hn : ∀ τ, s' τ + (lam τ).detShift = (n τ : ℤ)) (hs : ∀ τ, (lam' τ).detShift = -s τ)
    (hV : JetInVV X.K lam lam' n) (J : (DVar X.Tau a b →₀ ℕ) → X.K) (c : ℂ) (hJ : ∀ m, (∀ τ, degAt m τ = opDeg lam n τ) → σ₀ (J m) = c * jetC cD Θ m) (P : VV X.K lam) :
    evV X.emb 1 lam' σ₀ (jetOp lam lam' J n P) =
      c • mulFun (fun y' => (dePow σ₀ b s y')⁻¹) (unfTh σ₀ cD Θ (mulFun (dePow σ₀ a s') (evV X.emb 1 lam σ₀ P))) := by
  have hloc : jetMap (fun m => σ₀ (J m)) n (MvPolynomial.map σ₀ (P : Pol X.K X.Tau a)) = jetMap (fun m => c * jetC cD Θ m) n (MvPolynomial.map σ₀ (P : Pol X.K X.Tau a)) :=
    jet_local_rationality ℂ X.Tau a b lam n _ _ hJ _ (map_mem_VV σ₀ lam (P : Pol X.K X.Tau a) P.2)
  rw [sharp_evV σ₀ lam n s' hn P, unfTh_polFn, jetMap_shift]
  funext y'
  show evFr _ (shiftOf lam') σ₀ (jetOp lam lam' J n P).1 y' = c * ((dePow σ₀ b s y')⁻¹ * polFn σ₀ b _ y')
  rw [evFr_apply, jetOp_coe lam lam' n hV, ← eval_map, map_jetMap, hloc, jetMap_smul, smul_eval, polFn_apply]
  have hd : (∏ τ, (y'.1 τ).det ^ shiftOf lam' τ) = (dePow σ₀ b s y')⁻¹ := by
    unfold dePow
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    show (y'.1 τ).det ^ (lam' τ).detShift = ((y'.1 τ).det ^ s τ)⁻¹
    rw [hs, _root_.zpow_neg]
  rw [hd]
  ring

theorem unfTh_kerOfD (Am : Amb X) (σ₀ : X.K →+* ℂ) (hσ : Am.σ₀ = σ₀) (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (hA : 0 < cA) (hB : 0 < cB)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) (s' s : X.Tau → ℤ)
    (hn : ∀ τ, s' τ + (lam τ).detShift = (n τ : ℤ)) (hs : ∀ τ, (lam' τ).detShift = -s τ) (hV : JetInVV X.K lam lam' n)
    (hsm : Am.ESmooth a b) (hrat : Am.JetsRatDeg a b Sall (cA * cB) (opDeg lam n))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB) (hN : IsSdLat N) (hN' : IsSdLat N')
    (Ξ : HomE X.E a b → X.K) (P : VV X.K lam) :
    evV X.emb 1 lam' σ₀ (kerOf (thDistC Am Sall SB (cA * cB) sel mU mI lam lam' n) Sall cA cB N fr N' fr' Ξ P) =
      (σ₀ (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) * (Am.chiF a b N N')⁻¹) •
        mulFun (fun y' => (dePow σ₀ b s y')⁻¹)
          (unfTh σ₀ Am.cD (Am.thDat Sall cA cB N N' Ξ) (mulFun (dePow σ₀ a s') (evV X.emb 1 lam σ₀ P))) := by
  subst hσ
  rw [kerOf_tab Am Sall SB cA cB hA hB sel mU mI lam lam' n N fr N' fr' hN hN' Ξ, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    unfTh_evD Am.σ₀ Am.cD (Am.thDat Sall cA cB N N' Ξ) lam lam' n s' s hn hs hV _ (Am.chiF a b N N')⁻¹
      (kernel_table_spec_degree X Am a b Sall cA cB _ hA hB hsm hrat N N' hN hN' Ξ) P, smul_smul]

end Ev

section Wt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem unfTh_stepCD (Am : Amb X) (σ₀ : X.K →+* ℂ) (hσ : Am.σ₀ = σ₀) (u : Pr.Word) (hT : 0 < Pr.T u) {i : ℕ} (hi : i < R.m)
    (hV : JetInVVStep W u i (W.lamTrue u (i + 1))) (hsm : Am.ESmooth (R.N i) (R.N (i + 1)))
    (hrat : Am.JetsRatDeg (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i))
    (N : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (N' : Submodule (𝓞 X.E) (Sp X.E (R.N (i + 1))))
    (fr' : Frs X.E (R.N (i + 1)) (rowSG Pr sel mu)) (hN : IsSdLat N) (hN' : IsSdLat N') (Ξ : HomE X.E (R.N i) (R.N (i + 1)) → X.K)
    (P : VV X.K (W.lamTrue u i)) :
    evV X.emb 1 (W.lamTrue u (i + 1)) σ₀
        (kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N fr N' fr' Ξ P) =
      (σ₀ (scalK Ch sel mu cst i N fr N' fr') * (Am.chiF (R.N i) (R.N (i + 1)) N N')⁻¹) •
        mulFun (fun y' => (dePow σ₀ (R.N (i + 1)) (sDivC W u i) y')⁻¹)
          (unfTh σ₀ Am.cD (Am.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ)
            (mulFun (dePow σ₀ (R.N i) (sSharpC W u i)) (evV X.emb 1 (W.lamTrue u i) σ₀ P))) :=
  unfTh_kerOfD Am σ₀ hσ (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) (cAof_pos sel mu cst) (cBof_pos sel mu cst u hT) sel
    (mUof Ch mu i) (muAt Ch sel mu cst i) (W.lamTrue u i) (W.lamTrue u (i + 1)) (nuLast W u i) (sSharpC W u i) (sDivC W u i)
    (sSharpC_add W u hi) (lamTrue_last W u hi) hV hsm hrat N fr N' fr' hN hN' Ξ P

end Wt

end Formalism.L2.Col

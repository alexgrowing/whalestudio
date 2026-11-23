import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RegularisedThetaPairingIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoxProductsOrthogonalSumTargetCartanFockStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingWittTowerReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVacuumVectorPrincipalCongruenceSupportStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeffAtNegOneZetaOfEisCoeffAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Exh.Top

variable {D : D7}

theorem fockVec_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A H : HSp D} {sA : RealMat A} {sH : RealMat H}
    {f : WO A H → ℂ} (hf : IsThetaFunO ψ A H f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) : IsFockVec ψ θ A H sA sH f := by
  refine ⟨hf, 1, fun l hl => ?_⟩
  match l, hl with
  | [p], _ => exact hv p.1 p.2

theorem sphFun_of_param {V : HSp D} {Λ : Lat V} {Sf : Finset (FinPl D)} {f : GA D V → ℂ}
    {B : GlobalTheory.LFun.Fam D.host.E} (hf : GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (FinPl D)) f B) :
    SphFun V Λ Sf f := by
  intro v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

theorem downNe_of_hypotheses : GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm →
    GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D := by
  intro hDM hRSW hSP D hER ψ θ A W t χA χW om cA a β Z m u par sW Φ hDef hSigW hW0 hrank hη hom hPl hm hForm hOcc hNo
  obtain ⟨H, B, o, hd, hSigH, hSigB, hHr, hHsig, sH, hsH⟩ := GlobalTheory.T.exists_sum_hyperbolicPlanes_orthogonal_wittDecomposition D W t hSigW
  obtain ⟨c, hHyp⟩ := hForm.str
  have ht : W.rank + 5 ≤ t := hHyp.2.1
  have hBr : B.rank = W.rank + 2 * t := by have := o.rank_add; omega
  have hstd : IsStdChar D ψ (-1) := hom.std
  have h1 : IsHeckeChar D (1 : (AE D)ˣ →* Circle) := ⟨continuous_const, fun _ => rfl⟩
  have hr1 : ResEta D (1 : (AE D)ˣ →* Circle) 0 := by
    have h := resEta_parity (m := 0) (resEta_mul hom.resS (resEta_inv hom.resS)) (by omega)
    rwa [show χA * χA⁻¹ = 1 from mul_inv_cancel χA] at h
  obtain ⟨omH, homH⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ A H χA 1 hstd hom.hecS h1 hom.resS
    (resEta_parity hr1 (by omega))
  obtain ⟨omB, homB⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ A B χA χW hstd hom.hecS hom.hecT hom.resS
    (resEta_parity hom.resT (by omega))
  obtain ⟨omhB, homhB⟩ :=
    GlobalTheory.Core.Rk.exists_doubled_weilDatum GlobalTheory.weilRepresentationUnitaryPair D ψ A B χA χW omB homB
  obtain ⟨omhW, homhW⟩ :=
    GlobalTheory.Core.Rk.exists_doubled_weilDatum GlobalTheory.weilRepresentationUnitaryPair D ψ A W χA χW om hom
  have hAH : A.rank ≤ H.rank := by omega
  obtain ⟨f, hf, hf0, hfvac, hfsph, hfκ, hfoff⟩ :=
    GlobalTheory.T.exists_vacuumVector_principalCongruenceSupport D ψ θ A H χA omH (fun _ => 1) sH hDef.inf hη homH hDef.one hsH hAH β Z hPl
  have hfb := GlobalTheory.T.definite_real_group_fixes_split_space_weil_vacuum D ψ θ A H t χA omH sH hDef.inf hη homH hDef.one hsH hSigH hHr hHsig f hf hfvac
  obtain ⟨sB, LB, hsB, hLB, hbF, hbS⟩ :=
    GlobalTheory.T.boxProducts_orthogonalSum_target_cartan_fock D ψ θ A B W H o (fun _ => 1) sW sH hstd hDef.inf hOcc.cart hsH
  have hFs : IsFockVec ψ θ A B (fun _ => 1) sB (o.boxT A Φ f) := hbF Φ f hOcc.fock (fockVec_of_vac hf hfvac)
  have hSs : IsSphOff ψ A B (frameLat A) LB (under Z) (o.boxT A Φ f) :=
    hbS (frameLat A) (under Z) Φ f hOcc.sph hfsph
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank A.rank
  have hPair : Pair ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 :=
    { setting := ⟨by omega, by omega, by omega, hDef.inf, hDef.sig, hDef.cart, hDef.one, hsB, hDef.cA_eq⟩
      maj := hDef.maj
      maj_eq := hDef.maj_eq
      weil := homB
      covol := hν }
  have hu := hForm.mem
  have hu' := (Submodule.mem_inf.1 hu).2
  have huc : Continuous u := hu'.1
  have hul : ∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g := hu'.2.1
  have hKill := GlobalTheory.T.doubling_integrals_vanish_of_all_lifts_vanish D ψ A W χA χW om omhW hDef.sig hDef.pos hom homhW m hm u huc hul hNo
  have hφθ := GlobalTheory.Core.Rk.DeltaTheta.main D ψ A B hstd _ _ hFs.1 hFs.1
  have hφK := GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 hPair omhB homhB _ _ hFs hFs
  obtain ⟨hPole, E₁, hE₁, hE₁0⟩ := GlobalTheory.T.doubling_witt_tower_reduction hRSW D ψ θ A cA a hDef hPl.two B W t hd hSigB hSigW hW0
    (by omega) hrank χW omhB omhW homhB homhW ν 𝓕 hν m hm u huc hul hKill _ hφθ hφK
  obtain ⟨hZF, hEC, hAn, hReg, hint⟩ :=
    GlobalTheory.T.regularised_theta_pairing_identity hDM D ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 hPair omhB homhB m hm _ hFs u hu
  obtain ⟨hcc, -⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hDef.sig hDef.pos m hm
  have hRD := (GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D A hcc (fun g => conj (u g))
    ⟨fun γ hγ g => by simp only [hul γ hγ g], Complex.continuous_conj.comp huc⟩).1
  have hμ : IsHeckeChar D χW⁻¹ :=
    ⟨(hom.hecT.1.inv : Continuous fun x => (χW x)⁻¹), fun x => by rw [MonoidHom.inv_apply, hom.hecT.2 x, inv_one]⟩
  have hcoef := GlobalTheory.Eis.coeffAt_neg_one_zeta_of_eisCoeffAt D A χW⁻¹ hμ m hm _ hEC hAn hReg _ _ hRD hRD hZF
    (sZero A B) E₁ hPole hE₁
  rw [hE₁0] at hcoef
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.levelPlaces_integral_nonzero_constant D ψ θ A cA a hDef B W H o χA χW omB om omH homB hom homH β Z hPl m hm u hu
    hForm.fix sW Φ hOcc f hf hf0 hfκ hfb hfoff ν 𝓕 hν
  have hsph : SphFun A (frameLat A) (under Z) u := sphFun_of_param hForm.param
  have hUn : Unram ψ A B χW (frameLat A) LB (under Z) (o.boxT A Φ f) (o.boxT A Φ f) :=
    ⟨GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A, hLB, fun v _ h2 => hPl.two v h2, hForm.unr, hSs, hSs⟩
  have hEq : EqRight (GlobalTheory.Eis.zeta A χW⁻¹ m (flat A a (swSec A B omhB ν 𝓕 (delta A B (o.boxT A Φ f) (o.boxT A Φ f)))
      (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)))
      (fun s => GlobalTheory.LFun.LSD D (under Z) par χW (s + 1 / 2) /
        GlobalTheory.LFun.dSfun D.host.E (under Z : Set (FinPl D)) A.rank B.rank s * C) := by
    refine ⟨A.rank + 1, fun s hs => ?_⟩
    have hs' : (A.rank : ℝ) + 1 < s.re := hs
    have h2 : (A.rank : ℝ) / 2 < s.re := by
      have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
      linarith
    obtain ⟨hI, hz⟩ := hint s h2
    rw [hz, hER ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 hPair (frameLat A) LB (under Z) _ _ hFs.1 hFs.1 hUn
      m hm u hu u hu par hForm.param hsph s hs' hI, hC s]
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    simp only [sZero]
    rw [hBr, hrank]
    push_cast
    ring
  have hcoef' : CoeffAt (GlobalTheory.Eis.zeta A χW⁻¹ m (flat A a (swSec A B omhB ν 𝓕 (delta A B (o.boxT A Φ f) (o.boxT A Φ f)))
      (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g))) ((t : ℂ) / 2) (-1) 0 := by
    rw [← hs0]
    exact hcoef
  exact GlobalTheory.T.zeta_residue_ne_zero_of_simple_pole_lift_L_function hSP D (under Z) W.rank t c par χW hHyp A.rank B.rank _ C _ hC0 hEq hcoef' rfl

end GlobalTheory.Core.Rk.Exh.Top

end

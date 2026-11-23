import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMemStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.Exh

theorem zeta_eq_integral_integrand : GlobalTheory.Published.DoublingMethod → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → ∀ u ∈ A0 θ A cA, GlobalTheory.Eis.IsZetaFamily A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)) ∧ GlobalTheory.Eis.EisContinues A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) ∧ (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) g) (rightOf (A.rank / 2))) ∧ (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) s₀ k) ∧ ∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s) m ∧ GlobalTheory.Eis.zeta A χB⁻¹ m (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)) s = ∫ g, integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s g ∂m := by
  intro hDM D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh m hm Φ hΦ u hu
  obtain ⟨ha, ht, hb, hθ, hSig, hCart, -⟩ := hP.setting
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A B χA χB om omh hP.weil homh
  have hCC := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  obtain ⟨hφ, -⟩ := hTC Φ Φ hΦ.1 hΦ.1
  have hK := GlobalTheory.T.doublingVector_fockPair_isCompactFinite D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ Φ hΦ hΦ
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ Φ) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨hDM1, -, hDM3⟩ := hDM D A (by omega) a hP.maj hI χB⁻¹ B.rank hHk (resEta_inv homh.resT) (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ Φ)) hmem
  have hf := GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem D θ A cA hθ u hu
  obtain ⟨hBI, -⟩ := hDM3 θ hθ hSig cA hCart m hm _ hf _ hf
  have hpt : ∀ s g, flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B) s (io A (g, 1)) *
      conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u x)) (fun x => conj (u x)) g) =
      integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s g := by
    intro s g
    have e1 : swSec A B omh ν 𝓕 (delta A B Φ Φ) (io A (g, 1)) = wcoef om ν 𝓕 Φ Φ g :=
      (hCC Φ Φ hΦ.1 hΦ.1).2 g
    have e2 : conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u x)) (fun x => conj (u x)) g) = rcoef m u u g := by
      simp only [GlobalTheory.Eis.petCoef, rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend]
      rw [← integral_conj]
      congr 1
      funext q
      simp
    rw [integrand, ← e1, ← e2]
    rfl
  have hEF := hDM1.1.1
  refine ⟨⟨hEF, fun s hs => (hBI s hs).1⟩, hDM1.1, fun g => hEF.analyticOnNhd_flat g, hDM1.2, fun s hs => ?_⟩
  obtain ⟨-, hconv, heq⟩ := hBI s hs
  refine ⟨?_, ?_⟩
  · have e : integrand om m ν 𝓕 (frameLat A) a Φ Φ u u s = fun g =>
        flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B) s (io A (g, 1)) *
          starRingEnd ℂ (GlobalTheory.Eis.petCoef A m (fun x => conj (u x)) (fun x => conj (u x)) g) :=
      funext fun g => (hpt s g).symm
    rw [e]
    exact hconv
  · rw [GlobalTheory.Eis.zeta, heq]
    unfold zetaH pairInt
    exact integral_congr_ae (.of_forall fun g => hpt s g)

end GlobalTheory.Core.Rk.Exh

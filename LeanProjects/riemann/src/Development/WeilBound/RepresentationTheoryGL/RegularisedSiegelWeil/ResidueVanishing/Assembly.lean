import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Leaves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilDoubledSpaceOfStandardUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymmStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEqStatement
noncomputable section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PositivityTheory.Rg.Rsw.Kplug

set_option maxHeartbeats 1000000 in
theorem residue_vanishes_of_siegel_eisenstein : K0 → K1 → K2 → SimplePoleRescaling → ContinuousInvariantCoefficients → KillingPolyConst → ContinuationThroughChart → K4 →
    GlobalTheory.Published.SiegelEisensteinContinuation → PositivityTheory.Rg.Rsw.ResCore → ResidueVanishing := by
  intro k0 k1 k2 k2b k2c k3a k3b k4 hP hC D ψ θ A cA a hDef _ B W t hd _ _ hW0 _ hA h2 hlt χ omB omW hWB hWW ν 𝓕 hν m hm u hu hinv hK φ hφ hKφ
  have hrk := hd.rank_add
  have hIw := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a hDef.maj
  have hχ := GlobalTheory.T.isHeckeChar_restrictionEta_inv D χ W.rank hWW.hecT hWW.resT
  obtain ⟨hEC, hReg⟩ := hP D A (by omega) a hDef.maj hIw χ⁻¹ W.rank hχ.1 hχ.2 _ _
    (k0 D ψ A B χ omB hWB ν 𝓕 hν a hDef.maj φ hφ hKφ)
  obtain ⟨U, d, E, ε, hU, hR, hs, hd0, hhol, hc, hi, he, hrad⟩ :=
    k1 D A _ hEC hReg (fun g => hEC.1.analyticOnNhd_flat g) (sZero A B)
  obtain ⟨m0, hm0, hp0⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_standardUnitaryChart_doubledSpace D A m0 hm0
  obtain ⟨p, hp⟩ := hp0 A a hDef.maj κ hκ
  obtain ⟨lam, hlam, hψ', -⟩ := GlobalTheory.T.shiftedAdditiveCharacter_archimedeanParameters D ψ hWB.std θ hDef.inf m0 hm0
  obtain ⟨oB, hTB⟩ := GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf κ
  obtain ⟨νW, 𝓨, hνW⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank A.rank
  obtain ⟨oW, hTW⟩ := GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf κ
  have hSB : IsWeilSch (shift ψ lam) χ⁻¹ θ B ν oB :=
    ⟨GlobalTheory.T.transportedSchrodinger_standardLeviAction D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam,
     GlobalTheory.T.transportedSchrodinger_siegelUnipotentAction D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam,
     GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam⟩
  have hSW : IsWeilSch (shift ψ lam) χ⁻¹ θ W νW oW :=
    ⟨GlobalTheory.T.transportedSchrodinger_standardLeviAction D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf m0 hm0 κ hκ oW hTW lam hlam,
     GlobalTheory.T.transportedSchrodinger_siegelUnipotentAction D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf m0 hm0 κ hκ oW hTW lam hlam,
     GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf m0 hm0 κ hκ oW hTW lam hlam⟩
  let Φ : schwartzA θ B.rank A.rank :=
    ⟨sch ψ A B ν 𝓕 (omB ((p : GA D (dblSp A))⁻¹, 1) φ),
      (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hWB.std θ hDef.inf A B ν 𝓕 hν).1 _ (hWB.om_pres _ φ hφ)⟩
  obtain ⟨-, hCont, hser⟩ := k3b D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam a hDef.maj p hp φ hφ hKφ Φ rfl
    U d E hU hR hs hd0 hhol hc hi he
  obtain ⟨hH, hL⟩ := k3a D A m0 hm0 κ hκ a hDef.maj p hp
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    have hBr : B.rank = W.rank + 2 * t := by omega
    simp only [sZero]; rw [hBr, hA]; push_cast; ring
  obtain ⟨hcc, hcl⟩ := k2c D _ _ _ _ _ _ _ _ hCont ε hrad 1
  have hCont' := hCont
  have hrad' := hrad
  rw [hs0] at hCont' hrad'
  obtain ⟨hv, hkill⟩ := hC D A.rank t B W ⟨hd⟩ hA.symm h2 hlt hW0 (shift ψ lam) hψ' χ⁻¹ hχ.1 hχ.2 θ hDef.inf ν νW
    ⟨𝓕, hν⟩ ⟨𝓨, hνW⟩ oB oW hSB hSW _ hH hL Φ U d _ _ hCont' ε hrad'
  rw [← hs0] at hv hkill
  refine ⟨fun g => cf d (fun z g => npow (absA D (aP A p)) (z - sZero A B) * E z (κ.symm g * ((p : GA D (dblSp A))⁻¹)))
    (sZero A B) ε 1 (κ (g * p)), ⟨hEC.1, fun g => ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := k2 _ _ U d (sZero A B) ε _ hU hR (hCont.hol (κ (g * p))) hd0 hrad
      (fun z hz => hCont.eq z hz (κ (g * p))) (fun k hk => congrFun (hv k hk) (κ (g * p)))
    exact k2b _ _ _ _ _ _ (hom_pos _ _) h1 h2 (fun s hs => hser s hs g)
  · exact k4 D ψ θ A cA a hDef W χ omW hWW νW 𝓨 hνW m0 hm0 κ hκ oW hTW p m hm u hu hinv hK _ hcc hcl
      (fun X _ νX _ c hc hcp w hw h0 => hkill X νX c w hc hcp hw h0)

end PositivityTheory.Rg.Rsw.Kplug

end

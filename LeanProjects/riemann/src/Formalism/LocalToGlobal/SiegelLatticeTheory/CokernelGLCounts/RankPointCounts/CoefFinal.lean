import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPh
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefVol

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem nu_not_class_holds : FCount.NuNotCls M δ u u' F0 what₂ :=
  FCount.nuNotCls_of (fun Zd => PCount.inOrbZ_holds Zd u u')

theorem local_class_holds (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂) : LocClsE M δ u u' F0 what₂ :=
  locClsE_of hA hT hrows hN (fun Zd => PCount.inOrbZ_holds Zd u u')

theorem coefProd_of_steps (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hM : Formalism.L2.SG.Pf.NormRepMove D u u') (hPL : PhaseLoc M δ u u' F0 what₂) (hPP : PsiProdE D)
    (hV : VolProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ :=
  coefProd_of hA (local_class_holds hA hT hrows hN) (phase_class_holds M δ)
    (phaseProd_of hrows hN (Formalism.L2.SG.Pf.phase_well_defined hM hrows) (phaseAtRep_of hPL hPP)) hV

theorem coefficient_product_of_local (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hM : Formalism.L2.SG.Pf.NormRepMove D u u') (hPL : PhaseLoc M δ u u' F0 what₂) (hPP : PsiProdE D)
    (hVP : VolIdxProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ :=
  coefProd_of_steps hA hT hrows hN hM hPL hPP (volProd_of hA hT hrows hN (local_class_holds hA hT hrows hN) hVP)

end Formalism.L2.SG.Pf.Coef

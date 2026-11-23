import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormRepX

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section P

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def CtxP : Prop :=
  (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ IsRowReps D F0 what₂ ∧ Lat.PrimeHyp D u (Tu D u')

def FrGlobP : Prop := CtxP u u' F0 what₂ → FrGlob Zd u u' F0 what₂

def TauOneReduction : Prop := CtxP u u' F0 what₂ → Tau1 Zd u u' F0 what₂

def ExistP : Prop := CtxP u u' F0 what₂ → Exist Zd.M Zd.δ u u'

def SumFrP : Prop := CtxP u u' F0 what₂ → SumFr Zd.M Zd.δ u u' F0 what₂

variable {u u' F0 what₂}

theorem normRepExists_ctx (h : CtxP u u' F0 what₂) : PairVal.NormRepExists D u u' F0 what₂ := normRepExists_of (NormRepX.norm_representative_holds D u u' h.2.2) (Formalism.L2.SG.Closed.TermFun_holds D u u') h.2.1

theorem frCount_ctx (hG : FrGlobP Zd u u' F0 what₂) (hI : IntGenP Zd) (hτ : TauOneReduction Zd u u' F0 what₂) (hT : PartnerIsomorphismCount Zd)
    (h : CtxP u u' F0 what₂) : FrCount Zd.M Zd.δ u u' F0 what₂ := pcount_frCount Zd (normRepExists_ctx h) h.2.1 (hG h) hI (inOrbZ_holds Zd u u') (hτ h) hT

theorem partnerCount_ctx {θ0 : ∀ p, Option ((Zd.M p).Cls D.R.rS)}
    (hU : LocUnram Zd.M Zd.δ u u' θ0) (hR : ThRestricted Zd.M Zd.δ u u' F0 what₂ θ0)
    (hE : ExistP Zd u u' F0 what₂) (hS : SumFrP Zd u u' F0 what₂)
    (hG : FrGlobP Zd u u' F0 what₂) (hI : IntGenP Zd) (hτ : TauOneReduction Zd u u' F0 what₂) (hT : PartnerIsomorphismCount Zd)
    (h : CtxP u u' F0 what₂) : PartnerCount Zd.M Zd.δ u u' F0 what₂ := partnerCount_of hU hR h.2.1 (normRepExists_ctx h) eligRel_holds
    (restr_of Zd.3 h.2.1 (normRepExists_ctx h) eligRel_holds) (hE h) (hS h) (frCount_ctx Zd hG hI hτ hT h)

end P

end Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem partnerCount_holds {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hrows : IsRowReps D F0 what₂)
    (hP : Lat.PrimeHyp D u (Tu D u')) {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LsDatumB.LocUnram M δ u u' θ0) (hR : LsDatumB.ThRestricted M δ u u' F0 what₂ θ0)
    (hE : PCount.ExistP ⟨δ, M, hA⟩ u u' F0 what₂) (hS : PCount.SumFrP ⟨δ, M, hA⟩ u u' F0 what₂)
    (hG : PCount.FrGlobP ⟨δ, M, hA⟩ u u' F0 what₂) (hI : PCount.IntGenP ⟨δ, M, hA⟩)
    (hτ : PCount.TauOneReduction ⟨δ, M, hA⟩ u u' F0 what₂) (hT : PCount.PartnerIsomorphismCount ⟨δ, M, hA⟩) :
    LsDatumB.PartnerCount M δ u u' F0 what₂ := PCount.partnerCount_ctx ⟨δ, M, hA⟩ hU hR hE hS hG hI hτ hT ⟨hc, hrows, hP⟩

end Formalism.L2.SG.Pf

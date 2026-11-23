import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwd

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def BwdTerm' : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ',
        (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) →
        IsTerm Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ AdmWit Λ₂ (gS D) (lf D F0) (liftF F'₂) 1 ∧
          IsGeneric Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ FrameOK D Λ₂ (liftF F'₂)

variable {u u' F0 what₂}

theorem bwdPair_of_term_beta (h2 : BwdTerm' Zd u u' F0 what₂) (h4 : BwdBeta Zd u u' F0 what₂) : BwdPair Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg
  obtain ⟨hT, hA, hG, hO⟩ := h2 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩
  have hE := mem_EZ_of hn γ.lam Λ₂ (gmap_eq_of_image himg) (liftF F'₂) Z hT hA hG hO hS.1
  obtain ⟨x, hx, hGx, β, hP, hs0, hsc⟩ := h4 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg
  have hPD : PD D γ.lam (lf D F0) u' (mapL n (isom_of_N0F hn) (liftF F'₂)) := ⟨hE.1.1, hE.1.2.1, hE.2.2.2.1⟩
  let pr : Corank.Pair D u u' F0 what₂ :=
    ⟨γ.lam, γ.mem, x, ⟨_, hPD⟩, hGx, hE.1.2.2, β, hP⟩
  refine ⟨⟨γ.lam, γ.mem, TermDef.mk _ _ _ ⟨_, hPD⟩⟩, ⟨pr, ?_, rfl, hs0, hsc⟩, hPD, rfl⟩
  exact congrArg (fun c => (⟨γ.lam, γ.mem, c⟩ : TermDef.Term D u u' F0 what₂)) hx

theorem bwdC_of_ctx (hC : CtxP u u' F0 what₂) (h1 : BwdN Zd u u' F0 what₂) (h2 : BwdTerm' Zd u u' F0 what₂)
    (h4 : BwdBeta Zd u u' F0 what₂) : BwdC Zd u u' F0 what₂ := by
  intro γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨n, hn, himg⟩ := h1 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨hT, hA, hG, hO⟩ := h2 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩
  refine ⟨mapL n (isom_of_N0F hn) (liftF F'₂),
    ⟨?_, bwdPair_of_term_beta Zd h2 h4 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg⟩, n, hn, ⟨fun a => rfl, rfl⟩, himg⟩
  exact mem_EZ_of hn γ.lam Λ₂ (gmap_eq_of_image himg) (liftF F'₂) Z hT hA hG hO hS.1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

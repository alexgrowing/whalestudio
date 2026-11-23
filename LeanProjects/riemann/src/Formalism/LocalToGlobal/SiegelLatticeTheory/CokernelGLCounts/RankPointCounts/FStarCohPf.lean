import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountP

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace CohCut

def t2 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (Λ : Submodule (Zd.M p).L.O (Vp D p)) : Loc.Term (Vp D p) (Zd.M p) D.R.rS :=
  ⟨Λ, (tLoc Zd p γ).f, locF' Zd p F'₂, (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def vP (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → Vp D p :=
  (locH Zd p).MMfam (t2 Zd p γ F'₂ ⊥)

end CohCut

open CohCut

def CohHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  Ctx γ Z ∧ ZhatL (lf D F0) F'₂ = Z ∧ starCompat γ F'₂ ∧
    ∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _) (φ' p)

variable (u u' F0 what₂)

def CohGen : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ (locH Zd p).IsGeneric (t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))}.Finite

def CohResp : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ (locH Zd p).Respects (tLoc Zd p γ) (t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam)) (LinearEquiv.refl _ _) (φ' p)}.Finite

def CohGood : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂)}.Finite

variable {u u' F0 what₂}

theorem locSet_eq_single {p : PlF D} {γ : TermDef.Term D u u' F0 what₂}
    {F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    {φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)}
    (hmem : lattice₂ D Zd.M p γ.lam ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ')
    (hN : Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂)) :
    locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ' = {lattice₂ D Zd.M p γ.lam} := by
  ext Λ₂
  rw [Set.mem_singleton_iff]
  constructor
  · intro h2
    have hL : (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f = (locH Zd p).Lset Λ₂ (tLoc Zd p γ).f := by
      have h := h2.2.1
      exact (Set.image_id _).symm.trans h
    have hX := Formalism.MainNotions.S.Loc.HermSp.CohU.X_le_MMfam (H := locH Zd p) (t2 Zd p γ F'₂ ⊥)
    exact (Formalism.MainNotions.S.Loc.HermSp.CohU.lat_eq_of_Lset hN hX hmem.1.1.1 h2.1.1.1 hmem.1.2.1 h2.1.2.1 hL).symm
  · intro h
    rw [h]
    exact hmem

theorem starCoh_of (hP : CtxP u u' F0 what₂) (hGen : CohGen Zd u u' F0 what₂) (hResp : CohResp Zd u u' F0 what₂)
    (hGood : CohGood Zd u u' F0 what₂) : StarCoh Zd u u' F0 what₂ := by
  intro γ Z hC F'₂ hZ hc φ' hφ'
  have hH : CohHyp Zd γ Z F'₂ φ' := ⟨hC, hZ, hc, hφ'⟩
  refine ⟨γ.lam, (hP.2.1.1 γ.lam γ.mem).1.1, ?_⟩
  refine (((hGen hP γ Z F'₂ φ' hH).union (hResp hP γ Z F'₂ φ' hH)).union (hGood hP γ Z F'₂ φ' hH)).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  obtain ⟨⟨hg, hr⟩, hN⟩ := hn
  exact hp (locSet_eq_single Zd ⟨hg, hr⟩ hN)

theorem starCoh_of_P (hGen : CohGen Zd u u' F0 what₂) (hResp : CohResp Zd u u' F0 what₂)
    (hGood : CohGood Zd u u' F0 what₂) : CtxP u u' F0 what₂ → StarCoh Zd u u' F0 what₂ :=
  fun hP => starCoh_of Zd hP hGen hResp hGood

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

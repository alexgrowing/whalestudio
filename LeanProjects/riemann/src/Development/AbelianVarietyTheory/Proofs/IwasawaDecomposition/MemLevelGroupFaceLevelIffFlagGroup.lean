import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.TopBridge

variable {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

theorem rangeRestrict_mem_Q_iff (κ : GA D V) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q ↔ Lev.finE V κ ∈ parLev D.sp.cm V.gram β L := by
  have e1 : Lev.finE V κ = Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 := Lev.finE_eq V κ
  constructor
  · intro h
    have h1 : Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 ∈ lev D.sp.cm V.gram β (Lev.flagL L) := h
    rw [e1]
    exact h1.1
  · intro h
    have h1 : Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1 ∈ lev D.sp.cm V.gram β (Lev.flagL L) := by
      rw [mem_lev]
      exact ⟨e1 ▸ h, Subgroup.mem_top _⟩
    exact h1

theorem mem_levelSubgroup_withP_iff (P : LevelP L.Pg L.r ℂ) {κ : GA D V} (hκ : κ ∈ GfC V) :
    κ ∈ levS V β (Lev.withP L P) ↔ Lev.finE V κ ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (Lev.finE V κ) ∈ P.H :=
  ⟨fun h => h.2, fun h => ⟨hκ, h⟩⟩

theorem levelCharacter_withLevel_of_mem {P : LevelP L.Pg L.r ℂ} {κ : GA D V} (hp : rTup β L (Lev.finE V κ) ∈ P.H) :
    Lev.levChi V β (Lev.withP L P) κ = ((P.chi ⟨_, hp⟩ : ℂˣ) : ℂ) * Lev.levChi V β (Lev.flagL L) κ := by
  unfold Lev.levChi
  rw [Lev.levFn_withP, extendOne_of_mem _ hp, Units.val_mul]

theorem levChi_flagL_eq_ch {κ : GA D V} (hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q) :
    Lev.levChi V β (Lev.flagL L) κ = (((levEnv V β L).ch ⟨_, hq⟩ : ℂˣ) : ℂ) := by
  have e2 : (levEnv V β L).ch ⟨_, hq⟩ = levFn β (Lev.flagL L) (Formalism.UG.bc (swapAE D) ((finHom V).rangeRestrict κ).1) := rfl
  unfold Lev.levChi
  rw [e2, Lev.finE_eq]
  rfl

end GlobalTheory.TopBridge

open GlobalTheory.TopBridge in

theorem GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_red_R → ∀ (b : Bool) (t : T) (κ : GA D D.sp.X'), κ ∈ GfC D.sp.X' → ((κ ∈ levS _ R.βX (datXP R t (R.levR F b)) ↔ ∃ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q, (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P) ∧ ∀ (hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hp : (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P), levChi _ R.βX (datXP R t (R.levR F b)) κ = ((levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hq⟩ : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hp⟩ : D.what₂.LLˣ) : D.what₂.LL)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hr b t κ hκ
  have hQ : ∀ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q,
      (R.B.R t).act_tie.red ⟨_, hq⟩ = R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)) := fun hq =>
    R.eG.eq_symm_apply.2 ((hr t ⟨_, hq⟩).trans (congrArg (rTup R.βX (R.datXt t)) (Lev.finE_eq D.sp.X' κ).symm))
  have hH : ∀ x, x ∈ (R.levR F b).H ↔ R.eG.symm x ∈ (F.lvl b).P := fun x => Iff.rfl
  have hS := mem_levelSubgroup_withP_iff D.sp.X' R.βX (R.datXt t) (R.levR F b) hκ
  refine ⟨hS.trans ?_, ?_⟩
  · constructor
    · rintro ⟨h1, h2⟩
      have hq := (rangeRestrict_mem_Q_iff D.sp.X' R.βX (R.datXt t) κ).2 h1
      exact ⟨hq, (hQ hq).symm ▸ (hH _).1 h2⟩
    · rintro ⟨hq, hp⟩
      exact ⟨(rangeRestrict_mem_Q_iff D.sp.X' R.βX (R.datXt t) κ).1 hq, (hH _).2 (hQ hq ▸ hp)⟩
  · intro hq hp
    have hP : rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ) ∈ (R.levR F b).H := (hH _).2 (hQ hq ▸ hp)
    refine (levelCharacter_withLevel_of_mem D.sp.X' R.βX (R.datXt t) hP).trans ?_
    refine (mul_comm _ _).trans (congrArg₂ (· * ·) (levChi_flagL_eq_ch _ _ _ hq) ?_)
    have e : (⟨_, hp⟩ : (F.lvl b).P) = ⟨R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)), (hH _).1 hP⟩ :=
      Subtype.ext (hQ hq)
    have key : (((R.levR F b).chi ⟨_, hP⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL (((F.lvl b).ψ ⟨R.eG.symm (rTup R.βX (R.datXt t) (Lev.finE D.sp.X' κ)), (hH _).1 hP⟩ : D.what₂.LLˣ) : D.what₂.LL) :=
      rfl
    exact key.trans (congrArg (fun p => D.what₂.embLL (((F.lvl b).ψ p : D.what₂.LLˣ) : D.what₂.LL)) e.symm)

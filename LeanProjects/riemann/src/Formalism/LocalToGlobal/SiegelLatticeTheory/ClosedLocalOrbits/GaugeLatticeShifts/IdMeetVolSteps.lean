import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKey

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

section Defs

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def concreteLevelAdelicSubset (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' := fun ha hb => hK.2.1 _ ha _ hb
  inv_mem' := fun ha => hK.2.2.1 _ ha

def UcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) : Subgroup X.B.I.Gf :=
  Formalism.L2.SG.Pf.NfinSub (I := X.B.I) X.eR (X.zR u) ⊓ (concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom

def RcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) : Subgroup X.B.I.GA :=
  Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ (Formalism.L2.SG.Pf.NinfSub (I := X.B.I) X.eR (X.zR u)).prod (UcS X u hK c)

def GcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) : Subgroup X.B.I.Ginf := (RcS X u hK c).map (MonoidHom.fst _ _)

end Defs

def NOinfEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), NOinf X u = (GcS X u hK (X.xu u) : Set X.B.I.Ginf)

def NOcolEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl),
    Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ =
      (GcS X u Y.hK (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) : Set X.B.I.Ginf)

def GcCountC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf), Countable (GcS X u hK c)

def FundMeasEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Γ : Subgroup X.B.I.Ginf) (Ω Ω' : Set X.B.I.Ginf),
    (Γ : Set X.B.I.Ginf) ⊆ X.NinfU u → Countable Γ → IsSFund X.B.I Γ Ω → IsSFund X.B.I Γ Ω' →
      X.muN u Ω = X.muN u Ω'

def IndexVolC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Γ Γ' : Subgroup X.B.I.Ginf) (Ω : Set X.B.I.Ginf),
    Γ' ≤ Γ → (Γ : Set X.B.I.Ginf) ⊆ X.NinfU u → Countable Γ → Γ'.relIndex Γ ≠ 0 → IsSFund X.B.I Γ Ω →
      ∃ Ω', IsSFund X.B.I Γ' Ω' ∧ X.muN u Ω' = (Γ'.relIndex Γ : ℝ≥0∞) * X.muN u Ω

def IndexTransferC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (g h : Hfin X u),
    (GcS X u hK ((h : X.B.I.Gf) * X.xu u)).relIndex (GcS X u hK ((g : X.B.I.Gf) * X.xu u)) =
        (UcS X u hK ((h : X.B.I.Gf) * X.xu u)).relIndex (UcS X u hK ((g : X.B.I.Gf) * X.xu u)) ∧
      (UcS X u hK ((h : X.B.I.Gf) * X.xu u)).relIndex (UcS X u hK ((g : X.B.I.Gf) * X.xu u)) ≠ 0

def ConjUC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (g : Hfin X u) (c : X.B.I.Gf),
    UcS X u hK ((g : X.B.I.Gf) * c) = (UcS X u hK c).map (MulAut.conj (g : X.B.I.Gf)).toMonoidHom

def GcFundC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (h : Hfin X u),
    ∃ Ω, IsSFund X.B.I (GcS X u Y.hK ((h : X.B.I.Gf) * X.xu u)) Ω

def GcConjC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK),
    (GcS X u hK ((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) * X.xu u) : Set X.B.I.Ginf) =
      (fun s => (γ : X.B.I.GA).1 * s * (γ : X.B.I.GA).1⁻¹) '' (GcS X u hK ((h : X.B.I.Gf) * X.xu u) : Set X.B.I.Ginf)

def HinfConjC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (h : X.B.I.Ginf), h ∈ Hinf X u → ∀ Ω : Set X.B.I.Ginf,
    MeasurableSet Ω → X.muN u ((fun s => h * s * h⁻¹) '' Ω) = X.muN u Ω

end Formalism.L2.SG.Pf.IdMeet

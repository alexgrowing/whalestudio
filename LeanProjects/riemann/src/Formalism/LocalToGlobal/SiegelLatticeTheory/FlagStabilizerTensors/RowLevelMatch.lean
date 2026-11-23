import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

noncomputable section

set_option linter.dupNamespace false
set_option linter.unusedVariables false

open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned

namespace Formalism.L2.SG.RowLevelMatch

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kap (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (k : X.B.I.Gf) : GA D (Yc D 0) :=
  (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0))

def LevelMatchA (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) : Prop :=
  ∀ k ∈ X.K2, kap X h t k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) ∧
    levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (kap X h t k) = star (X.chi2 k)

def IsRedHom (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (red : X.B.I.Gf → G0g D.nd) : Prop :=
  (∀ k ∈ X.B.I.Kset, GoodAt X k (red k)) ∧ (∀ k ∈ X.B.I.Kset, ∀ k' ∈ X.B.I.Kset, red (k * k') = red k * red k') ∧
    (∀ γ : G0g D.nd, ∃ k ∈ X.B.I.Kset, red k = γ) ∧ ∀ k ∈ X.B.I.Kset, (red k = 1 ↔ k ∈ X.B.I.Kg X.B.g)

def LevelMatchB (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (σ : G0g D.nd ≃* G')
    (red : X.B.I.Gf → G0g D.nd) : Prop :=
  IsRedHom X red ∧ ∀ k ∈ X.B.I.Kset,
    ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))),
    ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)),
    (T : MMap (MP R)) v (g * kap X h t k) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) ((T : MMap (MP R)) v) g

def LevelMatchC (R : RealDat D A Ks) (σ : G0g D.nd ≃* G') : Prop :=
  ∀ γ : G0g D.nd, star (D.ntypes.e0.coeff γ) = RealDat.eC (A := A) D.what₂.embLL (σ γ)

def RowLevelMatchAt (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) : Prop :=
  ∃ (σ : G0g D.nd ≃* G') (red : X.B.I.Gf → G0g D.nd),
    LevelMatchA R F X h t ∧ LevelMatchB R F X h t σ red ∧ LevelMatchC R σ

def RowLevelMatch (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : Prop :=
  ∃ t : GA D (D.sp.Y 0), RowLevelMatchAt R F X h t

end Formalism.L2.SG.RowLevelMatch

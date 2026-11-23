import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

variable {D : D7} {u : D.what₂.Word}

def chart0 (F : Formalism.L2.Forms.Forms0 D u) : GlobalTheory.AdForm.Chart D u 0 (Nat.zero_le _) where
  cl := (D.mem u).C.cls 0
  inc := id
  K := F.cls0.toChart
  eY := F.val0.eY

theorem rd_zero {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : Formalism.L2.Forms.FormsTiedSym D u Ch chOf)
    (θ : InfFam D) (β : Ch 0) : GlobalTheory.AdForm.rd F θ 0 (Nat.zero_le _) β = (chart0 F.to0).rd θ := by
  funext ψ y
  unfold GlobalTheory.AdForm.rd GlobalTheory.AdForm.chart
  rw [dif_pos (Or.inl rfl)]
  rfl

def IsTransportAdelicCorrection {X : HidaSetting D} {F : Formalism.L2.Forms.Forms0 D u} (tr : Formalism.L2.SG.ColDict.Transport X u F) (a : GA D (D.sp.X 0)) : Prop :=
  a ∈ GfC (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = tr.h0.1.1

def IsSymLev {Pg : Finset (Pl D.host.E)} (P : LevelP Pg D.R.r ℂ) : Prop :=
  ∃ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ0 ∧
    ∃ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π ∧
      (∀ g, g ∈ P.H ↔ reord π g ∈ (PsharpSym Pg D.R.r D.R.rS D.R.k ψ0).H) ∧
      ∀ g hg hg', P.chi ⟨g, hg⟩ = (PsharpSym Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨reord π g, hg'⟩

def IsTypePlaces (Pg : Finset (Pl D.host.E)) : Prop :=
  (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      ∃! PP, PP ∈ Pg ∧ PP.under (𝓞 D.host.F) = v

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)

def PinBot : Prop :=
  ∃ (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)),
    B.lev = d.B 0 D.R.rS h0 ∧ B.Adapted (S.tr u).wt ∧ IsTransportAdelicCorrection (S.tr u) a₀ ∧
    a ∈ GfC (D.sp.X 0) ∧ a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧
    Matches S.X S.inst (d.lev 0) (levChi (D.sp.Y 0) d.bot.β d.bot.L)
      (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) ∧
    d.rd 0 = (chart0 (F₀ u)).rd d.c.θ

end GlobalTheory.Core.Mi

end

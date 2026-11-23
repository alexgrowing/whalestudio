import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FamAllQ
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def LevTrace : Prop :=
  ∀ κ ∈ GfC (D.sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) κ = y.1.1 →
    ((y : GL _ _) ∈ (F0 W u).cls0.lev.U ↔
      (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ rJ W) ∧
    ∀ hy : (y : GL _ _) ∈ (F0 W u).cls0.lev.U, (((F0 W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) *
      rChi W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0)) = 1

structure BotTie {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) : Prop where
  lev : ∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, B.lev = f.c.B 0 D.R.rS h₀
  adapted : B.Adapted (W.S.tr u).wt
  norm : ∃ μ lam : D.host.E, μ * lam = -D.host.xi0 ^ (D.R.m / 2) ∧
    (∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
    ∀ j h, v.τ j h *ᵥ o.ζ₀ = lam • (f.c.bes j 0 h).ζ
  last : ∀ i, (G i).z₀ = fun r => (ofSplit (G i).q).pr (o.ζ₀ r)
  lat : ∀ p, p ∉ v.tP → GlobalTheory.FinPl.latV (D.sp.X 0) (f.g.x 0).L (· = p) = GlobalTheory.FinPl.latV (D.sp.X 0)
    ((F0 W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
      (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) (· = p)
  trace : LevTrace f B

def ChartZero : Prop :=
  ∀ t, ∃ α₀ : (f.t t).Ch 0, (∀ α, α = α₀) ∧ (f.t t).e 0 α₀ = Finsupp.single (f.g.b 0) 1 ∧
    (∀ φ, col0 f t φ ∈ (f.t t).Ram 0 ∧ ∀ y, (f.t t).rd 0 α₀ (col0 f t φ) y = (chart0 (F0 W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) ∧
    ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = col0 f t φ

end GlobalTheory.MiTop

end

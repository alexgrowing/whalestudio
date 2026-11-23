import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

structure LevAtZ (F : Formalism.L2.Forms.Forms0 D u) : Prop where
  lat : ∀ z : Fin (D.sp.X 0).rank → D.host.E,
    (z ∈ (a.x 0).L ∧ ∀ i, (o.β 0 i).b' *ᵥ (fun r => (o.p i).pr (incA D (z r))) ∈ (o.Q 0 i).ker) ↔
    (fun i => z (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)).symm i)) ∈ F.cls0.lev.Lb
  lev : ∀ κ ∈ GfC (D.sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) κ = y.1.1 →
    ((y : GL _ _) ∈ F.cls0.lev.U ↔ InLev0 o G κ) ∧
    ∀ (hy : (y : GL _ _) ∈ F.cls0.lev.U) (g : ∀ PP : a.c.Pg, GL (XIx (Fin D.R.k) (Fin D.R.t) 0) (G PP).k)
      (hg : ∀ PP, embX ((G PP).s + 1) (g PP) ∈ (G PP).lev0.J), (∀ PP, (G PP).MatAt κ (g PP)) →
      ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) * ∏ PP, (((G PP).lev0.lam ⟨_, hg PP⟩ : ℂˣ) : ℂ) = 1

section World

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk

def LevZ {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (w : World I l Z) {v : B.Word}
    (a : XPart (I.rec7 l Z) v) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1) : Prop :=
  LevAtZ o G (w.C.forms v).to0 ∧ Arith o G

end World

end GlobalTheory.SeeSaw

end

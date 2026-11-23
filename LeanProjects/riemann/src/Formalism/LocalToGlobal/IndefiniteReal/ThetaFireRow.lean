import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FromLinks

open Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def MtRead (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (IL : LiftIds (toLiftReal R F tupT hm hTop hinj))
    (tw : ∀ μ (i : Fin D.R.m), D.what₂.MtL μ (i + 1) → A.fam.amb.FL i (tupT μ)) : Prop :=
  ∀ μ (hμ : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.MtL μ (i + 1)),
    (IL.jMt μ hμ i (D.what₂.jMt μ (i + 1) x)).1 = R.extV i (tupT μ) (R.jV i (tupT μ) (tw μ i x))

def ThetaFireL {D : D7} {C : ChainReal D} (L : LiftReal D C) (I : LiftIds L) : Prop :=
  ∀ μ (hμ : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i + 1)), ∃ w : L.AmbW i,
    w ∈ L.MultW i ∧ w ∘ₗ L.embK i = L.thC μ i (I.jMt μ hμ i x) ∧ L.eW i ∘ₗ w ∈ L.Wc i

def ResInjL {D : D7} {C : ChainReal D} (L : LiftReal D C) : Prop :=
  ∀ (i : Fin D.R.m) (w : L.AmbW i), w ∈ L.MultW i → w ∘ₗ L.embK i = 0 → w = 0

def ThetaFireRow {D : D7} {C : ChainReal D} (L : LiftReal D C) (I : LiftIds L) : Prop :=
  (∀ μ, Used0 D μ → ∀ i, Lift.IsThetaP (L.measV μ i) (L.fdV μ i) (L.thW μ i) (L.ptW μ i) (L.ioK i) (L.Amt μ i)
    (L.thC μ i)) ∧ ThetaFireL L I ∧ ResInjL L

def MjRead (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (IL : LiftIds (toLiftReal R F tupT hm hTop hinj))
    (nj : Fin D.R.m → ℕ) (crd : ∀ i : Fin D.R.m, (Fin (nj i) → D.what₂.LL) → D.what₂.Mj (i + 1))
    (jD : ∀ i : Fin D.R.m, (Fin (nj i) → D.what₂.LL) → (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  ∀ (i : Fin D.R.m) (y : Fin (nj i) → D.what₂.LL),
    ((IL.jMj i (crd i y) : (toLiftReal R F tupT hm hTop hinj).Wc i) : (toLiftReal R F tupT hm hTop hinj).AmbW i) =
      PiTensorProduct.lift (Mult.postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A))
        ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (jD i y))))

end FromLinks

end Formalism.IndefR.RecTie

end

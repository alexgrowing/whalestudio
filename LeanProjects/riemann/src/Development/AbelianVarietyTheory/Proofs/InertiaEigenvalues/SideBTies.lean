import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.SideTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fi
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def fiOf (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) : FormsIso (R.FW i') (R.FW i) := by
  subst h
  exact ⟨RingEquiv.refl _, fun _ => rfl, LinearEquiv.refl _ _, MulEquiv.refl _, fun _ => LinearIsometryEquiv.refl _ _,
    fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem fiOf_heq (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) (x : Fin (R.nW i') → D.what₂.LL) :
    HEq ((fiOf R i' i h).e x) x := by
  subst h; rfl

theorem fiOf_eG (R : RealDat3 D A3 Ks) (i' i : Fin D.R.m) (h : i' = i) (g : G) : (fiOf R i' i h).eG g = g := by
  subst h; rfl

end Fi

end GlobalTheory.TwInputs.SideTies

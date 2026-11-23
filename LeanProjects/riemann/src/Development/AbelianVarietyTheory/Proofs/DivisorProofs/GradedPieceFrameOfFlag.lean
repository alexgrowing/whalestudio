import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelSubbundleIsVB
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

set_option autoImplicit false

namespace GlobalTheory.FlagCell

theorem isFrame_π_of_spans : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (fl : Vert.Flag F r) (V : X.Opens)
    (e : Fin r → Γ(F, V)), Spans fl V e → ∀ (i : Fin r) (t : Γ(fl.F i.succ, V)),
    (fl.ι i.succ).app V t = e i → IsFrame fun _ : Fin 1 => (fl.π i).app V t := by
  intro X F r fl V e H i t ht
  obtain ⟨s, hs, es⟩ := H i.castSucc
  obtain ⟨s', hs', es'⟩ := H i.succ
  have e₁ (j : Fin i) : (fl.ι i.succ).app V ((fl.step i).app V (s j)) = e (Fin.castLE i.isLt.le j) := by
    refine Eq.trans ?_ (es j)
    rw [← fl.step_ι i]
    rfl
  have key := isFrame_cokernel_π (l := i) (m := 1) (fl.step i) hs' hs fun j =>
    QCoh.injective_app_of_mono (fl.ι i.succ) V ((e₁ j).trans (es' (Fin.castAdd 1 j)).symm)
  have htt : s' (Fin.natAdd i 0) = t := by
    refine QCoh.injective_app_of_mono (fl.ι i.succ) V ((es' _).trans (Eq.trans ?_ ht.symm))
    exact congrArg e (Fin.ext rfl)
  have hf : (fun _ : Fin 1 => (fl.π i).app V t) = fun k : Fin 1 => (cokernel.π (fl.step i)).app V (s' (Fin.natAdd i k)) := by
    funext k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    rw [htt]
    rfl
  rw [hf]
  exact key

end GlobalTheory.FlagCell

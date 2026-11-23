import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsContAutRTrans
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValOuter

open AddMonoidAlgebra in
theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (aconv (e :: l)) : AddMonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (aconv l) := by
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_ofCoeff]
  rfl

theorem aconv_nil {G : Type} [AddMonoid G] :
    (AddMonoidAlgebra.ofCoeff (aconv ([] : List (G →₀ ℂ))) : AddMonoidAlgebra ℂ G) = 1 := rfl

theorem aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) :
    (AddMonoidAlgebra.ofCoeff (aconv [c, d]) : AddMonoidAlgebra ℂ G) =
      AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d := by
  rw [aconv_cons, aconv_cons, aconv_nil, mul_one]

theorem aconv_pair_cons {G : Type} [AddMonoid G] (c d : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (aconv [c, d] :: l) = aconv (c :: d :: l) := by
  apply (AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := G))
  rw [aconv_cons, aconv_pair, aconv_cons, aconv_cons, mul_assoc]

theorem mem_support_aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) {u : G} (hu : u ∈ (aconv [c, d]).support) :
    ∃ a ∈ c.support, ∃ b ∈ d.support, a + b = u := by
  classical
  have h : (AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d : AddMonoidAlgebra ℂ G).coeff u ≠ 0 := by
    rw [← aconv_pair]; exact Finsupp.mem_support_iff.1 hu
  rw [AddMonoidAlgebra.coeff_mul] at h
  simp only [AddMonoidAlgebra.coeff_ofCoeff] at h
  obtain ⟨a, ha, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, hb, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hab : a + b = u
  · exact ⟨a, ha, b, hb, hab⟩
  · exact absurd (if_neg hab) h2

open MonoidAlgebra in
theorem conv_cons {G : Type} [Monoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (conv (e :: l)) : MonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (conv l) := by
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.coeff_finsuppSum]
  simp only [MonoidAlgebra.coeff_finsuppSum, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_ofCoeff]
  rfl

theorem conv_nil {G : Type} [Monoid G] :
    (MonoidAlgebra.ofCoeff (conv ([] : List (G →₀ ℂ))) : MonoidAlgebra ℂ G) = 1 := rfl

theorem mul_comm_of_support {G : Type} [Monoid G] (a b : MonoidAlgebra ℂ G)
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, x * y = y * x) : a * b = b * a := by
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.mul_def]
  unfold Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
  dsimp only
  rw [h x hx y hy, mul_comm (a.coeff x)]

theorem comm_conv {G : Type} [Monoid G] (E : G →₀ ℂ) (l : List (G →₀ ℂ))
    (h : ∀ x ∈ E.support, ∀ e ∈ l, ∀ y ∈ e.support, x * y = y * x) :
    (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff (conv l) =
      MonoidAlgebra.ofCoeff (conv l) * MonoidAlgebra.ofCoeff E := by
  induction l with
  | nil => rw [conv_nil, mul_one, one_mul]
  | cons e l ih =>
    have h1 : (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff e =
        MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff E :=
      mul_comm_of_support _ _ fun x hx y hy => h x hx e List.mem_cons_self y hy
    rw [conv_cons, ← mul_assoc, h1, mul_assoc, ih fun x hx e' he' y hy => h x hx e' (List.mem_cons_of_mem _ he') y hy,
      mul_assoc]

section Trc
variable {D : D7} {V : HSp D}

theorem trc_eq_sum (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc e f = e.sum fun g a => a • rTrans g f := rfl

theorem trc_single (g : GA D V) (a : ℂ) (f : GA D V → ℂ) : trc (Finsupp.single g a) f = a • rTrans g f := by
  rw [trc_eq_sum, Finsupp.sum_single_index]
  exact zero_smul _ _

theorem trc_zero (f : GA D V → ℂ) : trc (0 : GA D V →₀ ℂ) f = 0 := by
  simp [trc]

theorem trc_add (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (e + e') f = trc e f + trc e' f := by
  simp only [trc_eq_sum]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem trc_apply (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) : trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, Finset.sum_apply, rTrans]

theorem trc_add_right (e : GA D V →₀ ℂ) (f f' : GA D V → ℂ) : trc e (f + f') = trc e f + trc e f' := by
  funext x
  simp only [trc_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem trc_zero_right (e : GA D V →₀ ℂ) : trc e (0 : GA D V → ℂ) = 0 := by
  funext x
  simp [trc_apply]

theorem trc_mul (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) :
    trc (MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff e' : MonoidAlgebra ℂ (GA D V)).coeff f = trc e (trc e' f) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [MonoidAlgebra.ofCoeff_zero, zero_mul, MonoidAlgebra.coeff_zero, trc_zero, trc_zero]
  | add x y hx hy =>
    rw [MonoidAlgebra.ofCoeff_add, add_mul, MonoidAlgebra.coeff_add, trc_add, trc_add, hx, hy]
  | single g a =>
    induction e' using Finsupp.induction_linear with
    | zero => rw [MonoidAlgebra.ofCoeff_zero, mul_zero, MonoidAlgebra.coeff_zero, trc_zero, trc_zero_right]
    | add x y hx hy =>
      rw [MonoidAlgebra.ofCoeff_add, mul_add, MonoidAlgebra.coeff_add, trc_add, hx, hy, trc_add, trc_add_right]
    | single h b =>
      rw [MonoidAlgebra.ofCoeff_single, MonoidAlgebra.ofCoeff_single, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.coeff_single, trc_single, trc_single, trc_single]
      funext x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem contAut_trc (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ x => ?_, ?_⟩
  · simp only [trc_apply, mul_assoc, hf.1 γ hγ]
  · have : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := funext (trc_apply e f)
    rw [this]
    exact continuous_finset_sum _ fun g _ => (GlobalTheory.Core.Mi.BotPin.isContAut_rTrans g hf).2.const_smul (e g)

end Trc

end GlobalTheory.QValOuter
end

import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

def IsFlagSec (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x

def flagSec {K : Type} [Field K] (σ : K →+* ℂ) (X : Data E r) (la : Wt X.Ψ r) :
    Submodule K (FnVia σ (Frame X.Ψ r)) where
  carrier := {P | IsFlagSec X la P ∧ ∀ x, x ∉ X.dom → (show Frame X.Ψ r → ℂ from P) x = 0}
  zero_mem' := ⟨⟨differentiableOn_const (0 : ℂ), fun _ _ _ _ => (mul_zero _).symm⟩, fun _ _ => rfl⟩
  add_mem' := by
    intro P Q hP hQ
    refine ⟨⟨hP.1.1.add hQ.1.1, fun x hx b hb => ?_⟩, fun x hx => ?_⟩
    · change (show Frame X.Ψ r → ℂ from P) (rmul x b) + (show Frame X.Ψ r → ℂ from Q) (rmul x b) =
        bchar la b * ((show Frame X.Ψ r → ℂ from P) x + (show Frame X.Ψ r → ℂ from Q) x)
      rw [mul_add]
      exact congrArg₂ (· + ·) (hP.1.2 x hx b hb) (hQ.1.2 x hx b hb)
    · change (show Frame X.Ψ r → ℂ from P) x + (show Frame X.Ψ r → ℂ from Q) x = 0
      rw [hP.2 x hx, hQ.2 x hx, add_zero]
  smul_mem' := by
    intro a P hP
    refine ⟨⟨hP.1.1.const_mul (σ a), fun x hx b hb => ?_⟩, fun x hx => ?_⟩
    · change σ a * (show Frame X.Ψ r → ℂ from P) (rmul x b) =
        bchar la b * (σ a * (show Frame X.Ψ r → ℂ from P) x)
      rw [mul_left_comm]
      exact congrArg (σ a * ·) (hP.1.2 x hx b hb)
    · change σ a * (show Frame X.Ψ r → ℂ from P) x = 0
      rw [hP.2 x hx, mul_zero]

theorem zAct_rmul (X : Data E r) (cu : FJ.CuspFD X ρ) (t : Fin (nZ X ρ) → ℝ) (x b : Frame X.Ψ r) :
    zAct X cu t (rmul x b) = rmul (zAct X cu t x) b := by
  funext τ
  exact (Matrix.mul_assoc _ (mat x τ) (mat b τ)).symm

theorem isFlagSec_coefFn (X : Data E r) (la : Wt X.Ψ r) (cu : FJ.CuspFD X ρ)
    (hd : ∀ t, ∀ x ∈ X.dom, zAct X cu t x ∈ X.dom) (ph : Fin (nZ X ρ) → ℝ) {P : Frame X.Ψ r → ℂ}
    (hP : IsFlagSec X la P) : IsFlagSec X la (coefFn (zAct X cu) ph P) := by
  constructor
  · have hj : Continuous fun p : (Fin (nZ X ρ) → ℝ) × Frame X.Ψ r => zAct X cu p.1 p.2 := by
      unfold zAct zMatC mat
      fun_prop
    have hc : Continuous (chr ph) := by unfold chr; fun_prop
    refine (GlobalTheory.differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := volume)
      (F := fun t x => integrand (zAct X cu) ph P x t) (FourierCoefficientDomain.isOpen_dom X) (S := cube _) (K := cube _)
      isCompact_Icc subset_rfl measurableSet_Icc (isCompact_Icc.measure_lt_top.ne) ?_ ?_).1
    · refine ContinuousOn.mul (hP.1.continuousOn.comp hj.continuousOn fun p hp => hd p.1 p.2 hp.2) ?_
      exact (hc.comp continuous_fst).continuousOn
    · intro t _
      refine DifferentiableOn.mul_const (hP.1.comp ?_ fun x hx => hd t x hx) _
      refine Differentiable.differentiableOn ?_
      refine differentiable_pi.2 fun τ => differentiable_pi.2 fun i => differentiable_pi.2 fun k => ?_
      simp only [zAct, Matrix.mul_apply, mat, Matrix.of_apply]
      fun_prop
  · intro x hx b hb
    unfold coefFn integrand
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [zAct_rmul, hP.2 _ (hd t x hx) b hb, mul_assoc]

theorem coef_mem_flagSec {K : Type} [Field K] (σ : K →+* ℂ) (X : Data E r) (la : Wt X.Ψ r) (cu : FJ.CuspFD X ρ)
    (hd : ∀ t, ∀ x ∈ X.dom, zAct X cu t x ∈ X.dom) (ph : Fin (nZ X ρ) → ℝ) (P : OrbInt (zAct X cu) X.dom)
    (hP : IsFlagSec X la P) :
    (show FnVia σ (Frame X.Ψ r) from coefL (zAct X cu) X.dom ph P) ∈ flagSec σ X la := by
  have h := isFlagSec_coefFn X la cu hd ph hP
  refine ⟨⟨h.1.congr fun x hx => coefL_apply _ _ _ _ hx, fun x hx b hb => ?_⟩, fun x hx => ?_⟩
  · change coefL (zAct X cu) X.dom ph P (rmul x b) = bchar la b * coefL (zAct X cu) X.dom ph P x
    rw [coefL_apply _ _ _ _ hx, coefL_apply _ _ _ _ (dom_rmul X hx hb)]
    exact h.2 x hx b hb
  · change coefL (zAct X cu) X.dom ph P x = 0
    simp [coefL, hx]

end GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction

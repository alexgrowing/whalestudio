import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.GA

def nx : Multiplicative ℚ →* GL (Fin 2) ℚ where
  toFun x := ⟨!![1, x.toAdd; 0, 1], !![1, -x.toAdd; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def nU : Subgroup (GL (Fin 2) ℚ) := nx.range

abbrev NQ : Type := Quotient (QuotientGroup.rightRel nU)

def b1M : Matrix (Fin 2) (Fin 2) ℚ →* Matrix (Fin 3) (Fin 3) ℚ where
  toFun γ := !![γ 0 0, γ 0 1, 0; γ 1 0, γ 1 1, 0; 0, 0, 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def b2M : Matrix (Fin 2) (Fin 2) ℚ →* Matrix (Fin 3) (Fin 3) ℚ where
  toFun γ := !![1, 0, 0; 0, γ 0 0, γ 0 1; 0, γ 1 0, γ 1 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def e1 : GL (Fin 2) ℚ →* GL (Fin 3) ℚ := Units.map b1M

def e2 : GL (Fin 2) ℚ →* GL (Fin 3) ℚ := Units.map b2M

def sw : GL (Fin 3) ℚ :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def uS (W : G3 → ℂ) (g : G3) : ℂ := ∑' q : NQ, W (dia (e1 q.out) * g)

def vS (W : G3 → ℂ) (g : G3) : ℂ := ∑' q : NQ, W (dia (e2 q.out * sw) * g)

def lowM (c : 𝔸[ℚ]) : G3 :=
  ⟨!![1, 0, 0; c, 1, 0; 0, 0, 1], !![1, 0, 0; -c, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def yCoef (f : G3 → ℂ) (ξ : Fin 2 → ℚ) (g : G3) : ℂ :=
  ∫ y in vecDomain ℚ (Fin 2), f (uni 0 (y 0) (y 1) * g) * (adelicChar ℚ (-pair ξ y) : ℂ) ∂vecMeasure ℚ (Fin 2)

def ctY (f : G3 → ℂ) (g : G3) : ℂ :=
  ∫ y in vecDomain ℚ (Fin 2), f (uni 0 (y 0) (y 1) * g) ∂vecMeasure ℚ (Fin 2)

def ctY' (f : G3 → ℂ) (g : G3) : ℂ :=
  ∫ y in vecDomain ℚ (Fin 2), f (lowM (y 0) * uni 0 0 (y 1) * g) ∂vecMeasure ℚ (Fin 2)

def hCoef (f : G3 → ℂ) (ξ : Fin 2 → ℚ) (g : G3) : ℂ :=
  ∫ y in vecDomain ℚ (Fin 3), f (lowM (y 0) * uni 0 (y 1) (y 2) * g) *
    (adelicChar ℚ (-(algebraMap ℚ 𝔸[ℚ] (ξ 0) * y 0 + algebraMap ℚ 𝔸[ℚ] (ξ 1) * y 1)) : ℂ) ∂vecMeasure ℚ (Fin 3)

def RInv (f : G3 → ℂ) : Prop :=
  ∀ p : GL (Fin 3) ℚ, p.val 0 1 = 0 → p.val 2 0 = 0 → p.val 2 1 = 0 → ∀ g, f (dia p * g) = f g

def ContW : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, Continuous W

def MajU : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ Kc : Set G3, IsCompact Kc →
  ∃ b : NQ → ℝ, Summable b ∧ ∀ q g, g ∈ Kc → ‖W (dia (e1 q.out) * g)‖ ≤ b q

def ContUV : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, Continuous (uS W) ∧ Continuous (vS W)

def MajV : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ Kc : Set G3, IsCompact Kc →
  ∃ b : NQ → ℝ, Summable b ∧ ∀ q g, g ∈ Kc → ‖W (dia (e2 q.out * sw) * g)‖ ≤ b q

def SmoothU : Prop := ∀ V (hV : WhA V), ∀ W (hW : W ∈ V), ∃ h : IsArchSmooth (uS W), ∀ i j,
  ((EA i j ⟨uS W, h⟩ : archSmooth ℚ 3) : G3 → ℂ) = uS ((EA i j ⟨W, hV.arch W hW⟩ : archSmooth ℚ 3) : G3 → ℂ)

def Growth : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, HasModerateGrowth (uS W)

def InvU : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ p : GL (Fin 3) ℚ, p.val 2 0 = 0 → p.val 2 1 = 0 →
  ∀ g, uS W (dia p * g) = uS W g

def InvV : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ p : GL (Fin 3) ℚ, p.val 0 1 = 0 → p.val 2 1 = 0 →
  ∀ g, vS W (dia p * g) = vS W g

def GenQ : Prop := ∀ H : Subgroup (GL (Fin 3) ℚ),
  (∀ p : GL (Fin 3) ℚ, p.val 2 0 = 0 → p.val 2 1 = 0 → p ∈ H) →
  (∀ p : GL (Fin 3) ℚ, p.val 0 1 = 0 → p.val 2 1 = 0 → p ∈ H) → H = ⊤

def YU : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ g,
  yCoef (uS W) ![0, 1] g = ∑' a : ℚˣ, W (dia (dg a 1 1) * g)

def YV : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ g,
  yCoef (vS W) ![0, 1] g = ∑' b : ℚˣ, ∫ u, W (dia (dg 1 1 b) * cyc u * g) ∂adeleMeasure ℚ

def Orbit : Prop := ∀ f : G3 → ℂ, Continuous f → RInv f → (∀ g, yCoef f ![0, 1] g = 0) →
  ∀ ξ : Fin 2 → ℚ, ξ 1 ≠ 0 → ∀ g, yCoef f ξ g = 0

def UpperRightUnipotentInvariance : Prop := ∀ f : G3 → ℂ, Continuous f → RInv f → (∀ ξ : Fin 2 → ℚ, ξ 1 ≠ 0 → ∀ g, yCoef f ξ g = 0) →
  ∀ (t : 𝔸[ℚ]) g, f (uni 0 0 t * g) = f g

def HeisZero : Prop := ∀ f : G3 → ℂ, Continuous f → RInv f → (∀ (t : 𝔸[ℚ]) g, f (uni 0 0 t * g) = f g) →
  (∀ ξ g, hCoef f ξ g = 0) → ∀ g, f g = 0

def HDeg : Prop := ∀ f : G3 → ℂ, Continuous f → RInv f → (∀ g, ctY f g = 0) → (∀ g, ctY' f g = 0) →
  ∀ ξ : Fin 2 → ℚ, (ξ 0 = 0 ∨ ξ 1 = 0) → ∀ g, hCoef f ξ g = 0

def CtU : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ g, ctY (uS W) g = 0 ∧ ctY' (uS W) g = 0

def CtV : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ g, ctY (vS W) g = 0 ∧ ctY' (vS W) g = 0

def HGen : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ ξ : Fin 2 → ℚ, ξ 0 ≠ 0 → ξ 1 ≠ 0 → ∀ g,
  hCoef (uS W) ξ g = hCoef (vS W) ξ g

def DZero : Prop := ∀ V (_ : WhA V), (∀ W ∈ V, Vor W) → ∀ W ∈ V, ∀ g, uS W g = vS W g

def ContUVOf : Prop := ContW → MajU → MajV → ContUV

def DZeroOf : Prop := ContW → MajU → MajV → InvU → InvV → YU → YV → Orbit → UpperRightUnipotentInvariance → HeisZero → HDeg →
  CtU → CtV → HGen → DZero

def Cusp : Prop := ∀ f : G3 → ℂ, Continuous f → IsLeftInvariant f → (∀ g, ctY f g = 0) → (∀ g, ctY' f g = 0) →
  IsCuspidal f

def WhitY : Prop := ∀ f : G3 → ℂ, Continuous f → ∀ g, FourierWhittaker.whittaker f g =
  ∫ x in vecDomain ℚ (Fin 1), yCoef f ![0, 1] (uni (x 0) 0 0 * g) * (adelicChar ℚ (-x 0) : ℂ) ∂vecMeasure ℚ (Fin 1)

def WhitU : Prop := ∀ V (_ : WhA V), ∀ W ∈ V, ∀ g,
  ∫ x in vecDomain ℚ (Fin 1), (∑' a : ℚˣ, W (dia (dg a 1 1) * (uni (x 0) 0 0 * g))) * (adelicChar ℚ (-x 0) : ℂ)
    ∂vecMeasure ℚ (Fin 1) = W g

end Ad3.GA

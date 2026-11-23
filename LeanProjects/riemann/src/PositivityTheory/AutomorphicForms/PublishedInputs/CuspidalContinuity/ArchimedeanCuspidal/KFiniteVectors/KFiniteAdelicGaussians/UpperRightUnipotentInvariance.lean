import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.K.GA

variable (K : Type) [Field K] [NumberField K]

def nx : Multiplicative K →* GL (Fin 2) K where
  toFun x := ⟨!![1, x.toAdd; 0, 1], !![1, -x.toAdd; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def nU : Subgroup (GL (Fin 2) K) := (nx K).range

abbrev NQ : Type := Quotient (QuotientGroup.rightRel (nU K))

def b1M : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun γ := !![γ 0 0, γ 0 1, 0; γ 1 0, γ 1 1, 0; 0, 0, 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def b2M : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun γ := !![1, 0, 0; 0, γ 0 0, γ 0 1; 0, γ 1 0, γ 1 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def e1 : GL (Fin 2) K →* GL (Fin 3) K := Units.map (b1M K)

def e2 : GL (Fin 2) K →* GL (Fin 3) K := Units.map (b2M K)

def sw : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

variable {K}

def uS (W : G3K K → ℂ) (g : G3K K) : ℂ := ∑' q : NQ K, W (diaK (e1 K q.out) * g)

def vS (W : G3K K → ℂ) (g : G3K K) : ℂ := ∑' q : NQ K, W (diaK (e2 K q.out * sw K) * g)

def lowM (c : 𝔸[K]) : G3K K :=
  ⟨!![1, 0, 0; c, 1, 0; 0, 0, 1], !![1, 0, 0; -c, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def yCoef (f : G3K K → ℂ) (ξ : Fin 2 → K) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 2), f (uni 0 (y 0) (y 1) * g) * (adelicChar K (-pair ξ y) : ℂ) ∂vecMeasure K (Fin 2)

def ctY (f : G3K K → ℂ) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 2), f (uni 0 (y 0) (y 1) * g) ∂vecMeasure K (Fin 2)

def ctY' (f : G3K K → ℂ) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 2), f (lowM (y 0) * uni 0 0 (y 1) * g) ∂vecMeasure K (Fin 2)

def hCoef (f : G3K K → ℂ) (ξ : Fin 2 → K) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 3), f (lowM (y 0) * uni 0 (y 1) (y 2) * g) *
    (adelicChar K (-(algebraMap K 𝔸[K] (ξ 0) * y 0 + algebraMap K 𝔸[K] (ξ 1) * y 1)) : ℂ) ∂vecMeasure K (Fin 3)

def RInv (f : G3K K → ℂ) : Prop :=
  ∀ p : GL (Fin 3) K, p.val 0 1 = 0 → p.val 2 0 = 0 → p.val 2 1 = 0 → ∀ g, f (diaK p * g) = f g

variable (K)

def ContW : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, Continuous W

def MajU : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ Kc : Set (G3K K), IsCompact Kc →
  ∃ b : NQ K → ℝ, Summable b ∧ ∀ q g, g ∈ Kc → ‖W (diaK (e1 K q.out) * g)‖ ≤ b q

def ContUV : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, Continuous (uS W) ∧ Continuous (vS W)

def MajV : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ Kc : Set (G3K K), IsCompact Kc →
  ∃ b : NQ K → ℝ, Summable b ∧ ∀ q g, g ∈ Kc → ‖W (diaK (e2 K q.out * sw K) * g)‖ ≤ b q

def SmoothU : Prop := ∀ V (hV : WhAK (K := K) V), ∀ W (hW : W ∈ V), ∃ h : IsArchSmooth (uS W), ∀ X,
  ((EAK X ⟨uS W, h⟩ : archSmooth K 3) : G3K K → ℂ) = uS ((EAK X ⟨W, hV.arch W hW⟩ : archSmooth K 3) : G3K K → ℂ)

def Growth : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, HasModerateGrowth (uS W)

def InvU : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ p : GL (Fin 3) K, p.val 2 0 = 0 → p.val 2 1 = 0 →
  ∀ g, uS W (diaK p * g) = uS W g

def InvV : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ p : GL (Fin 3) K, p.val 0 1 = 0 → p.val 2 1 = 0 →
  ∀ g, vS W (diaK p * g) = vS W g

def GenQ : Prop := ∀ H : Subgroup (GL (Fin 3) K),
  (∀ p : GL (Fin 3) K, p.val 2 0 = 0 → p.val 2 1 = 0 → p ∈ H) →
  (∀ p : GL (Fin 3) K, p.val 0 1 = 0 → p.val 2 1 = 0 → p ∈ H) → H = ⊤

def YU : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ g,
  yCoef (uS W) ![0, 1] g = ∑' a : Kˣ, W (diaK (dg a 1 1) * g)

def YV : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ g,
  yCoef (vS W) ![0, 1] g = ∑' b : Kˣ, ∫ u, W (diaK (dg 1 1 b) * cyc u * g) ∂adeleMeasure K

def Orbit : Prop := ∀ f : G3K K → ℂ, Continuous f → RInv f → (∀ g, yCoef f ![0, 1] g = 0) →
  ∀ ξ : Fin 2 → K, ξ 1 ≠ 0 → ∀ g, yCoef f ξ g = 0

def UpperRightUnipotentInvariance : Prop := ∀ f : G3K K → ℂ, Continuous f → RInv f → (∀ ξ : Fin 2 → K, ξ 1 ≠ 0 → ∀ g, yCoef f ξ g = 0) →
  ∀ (t : 𝔸[K]) g, f (uni 0 0 t * g) = f g

def HeisZero : Prop := ∀ f : G3K K → ℂ, Continuous f → RInv f → (∀ (t : 𝔸[K]) g, f (uni 0 0 t * g) = f g) →
  (∀ ξ g, hCoef f ξ g = 0) → ∀ g, f g = 0

def HDeg : Prop := ∀ f : G3K K → ℂ, Continuous f → RInv f → (∀ g, ctY f g = 0) → (∀ g, ctY' f g = 0) →
  ∀ ξ : Fin 2 → K, (ξ 0 = 0 ∨ ξ 1 = 0) → ∀ g, hCoef f ξ g = 0

def CtU : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ g, ctY (uS W) g = 0 ∧ ctY' (uS W) g = 0

def CtV : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ g, ctY (vS W) g = 0 ∧ ctY' (vS W) g = 0

def HGen : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ ξ : Fin 2 → K, ξ 0 ≠ 0 → ξ 1 ≠ 0 → ∀ g,
  hCoef (uS W) ξ g = hCoef (vS W) ξ g

def DZero : Prop := ∀ V (_ : WhAK (K := K) V), (∀ W ∈ V, VorK W) → ∀ W ∈ V, ∀ g, uS W g = vS W g

def ContUVOf : Prop := ContW K → MajU K → MajV K → ContUV K

def DZeroOf : Prop := ContW K → MajU K → MajV K → InvU K → InvV K → YU K → YV K → Orbit K → UpperRightUnipotentInvariance K →
  HeisZero K → HDeg K → CtU K → CtV K → HGen K → DZero K

def Cusp : Prop := ∀ f : G3K K → ℂ, Continuous f → IsLeftInvariant f → (∀ g, ctY f g = 0) → (∀ g, ctY' f g = 0) →
  IsCuspidal f

def WhitY : Prop := ∀ f : G3K K → ℂ, Continuous f → ∀ g, FourierWhittaker.whittaker f g =
  ∫ x in vecDomain K (Fin 1), yCoef f ![0, 1] (uni (x 0) 0 0 * g) * (adelicChar K (-x 0) : ℂ) ∂vecMeasure K (Fin 1)

def WhitU : Prop := ∀ V (_ : WhAK (K := K) V), ∀ W ∈ V, ∀ g,
  ∫ x in vecDomain K (Fin 1), (∑' a : Kˣ, W (diaK (dg a 1 1) * (uni (x 0) 0 0 * g))) * (adelicChar K (-x 0) : ℂ)
    ∂vecMeasure K (Fin 1) = W g

end Ad3.K.GA

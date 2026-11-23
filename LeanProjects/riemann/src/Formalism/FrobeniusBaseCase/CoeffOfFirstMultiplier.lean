import Formalism.FrobeniusBaseCase.Statement

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

def MulRule (k : Type*) [Field k] (Z : Type*) : Prop :=
  ∀ (v : AddValuation k (WithTop ℝ)) (r w1 w2 : ℝ) (f g : MvPowerSeries Z k),
    HasWt v r w1 f → HasWt v r w2 g → HasWt v r (w1 + w2) (f * g)

def PowRule (k : Type*) [Field k] (Z : Type*) : Prop :=
  ∀ (v : AddValuation k (WithTop ℝ)) (r w : ℝ) (f : MvPowerSeries Z k) (N : ℕ),
    HasWt v r w f → HasWt v r ((N : ℝ) * w) (f ^ N)

def HasWt2 {k : Type*} [Field k] {Z Z' : Type*} (v : AddValuation k (WithTop ℝ)) (r r' w : ℝ)
    (f : MvPowerSeries (Z ⊕ Z') k) : Prop :=
  ∀ (A : Z →₀ ℕ) (B : Z' →₀ ℕ), (w : WithTop ℝ) ≤ v (coeff (Finsupp.sumElim A B) f) +
    ((((A.degree : ℕ) : ℝ) * r + ((B.degree : ℕ) : ℝ) * r' : ℝ) : WithTop ℝ)

def MulRule2 (k : Type*) [Field k] (Z Z' : Type*) : Prop :=
  ∀ (v : AddValuation k (WithTop ℝ)) (r r' w1 w2 : ℝ) (f g : MvPowerSeries (Z ⊕ Z') k),
    HasWt2 v r r' w1 f → HasWt2 v r r' w2 g → HasWt2 v r r' (w1 + w2) (f * g)

def PowRule2 (k : Type*) [Field k] (Z Z' : Type*) : Prop :=
  ∀ (v : AddValuation k (WithTop ℝ)) (r r' w : ℝ) (f : MvPowerSeries (Z ⊕ Z') k) (N : ℕ),
    HasWt2 v r r' w f → HasWt2 v r r' ((N : ℝ) * w) (f ^ N)

namespace Data

variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

def CoeffOfFirstMultiplier : Prop := ∀ (d : Z) (b : C),
  coeff (D.q • Finsupp.single d 1) (D.m 1 b) = -(D.l : k)⁻¹ * D.g (D.ι d) b

def BaseCaseFalseGeneral : Prop := 2 ≤ D.K → ∀ (d : Z) (b : C), D.lev b = 1 →
  D.v (D.g (D.ι d) b) + ((qnum D.l * sg D.l D.i : ℝ) : WithTop ℝ) < 1 → ¬ D.InW D.zvec

def QSigmaSmall : Prop := 2 ≤ D.K → qnum D.l * sg D.l D.i < 1

end Data

end

end Formalism.BaseCaseIdentities

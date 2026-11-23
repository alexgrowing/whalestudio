import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def LineTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q₁ Q₂ : LineBundle S x), ∃ Q : LineBundle S x, Q.toSubSystem = Q₁.toSubSystem.twist Q₂.toSubSystem

def TwistAlg.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (M : SubSystem S x Ω) (p q : ℕ) (m m' : ℤ) (b₁ b₂ : ℕ), (q : ℤ) * m = p * m' →
    (twistMul M p m).pow (q * b₁ + b₂) =
      ((twistMul M p m).pow b₂).twist ((twistMul M q m').pow (p * b₁))

def RestrictTwist.Statement : Prop :=
  (∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := S) x ≤ primeOf (S := S) y → ∀ c : ℤ,
      ∃ r : Ω → K', RestrictData (twistSys S x c) hxy (twistSys S y c) r) ∧
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (Q₁ Q₂ : LineBundle S x) (Q₁' Q₂' : LineBundle S y) (r₁ r₂ : Ω → K'),
    RestrictData Q₁.toSubSystem hxy Q₁'.toSubSystem r₁ →
    RestrictData Q₂.toSubSystem hxy Q₂'.toSubSystem r₂ →
    ∃ r : Ω → K', RestrictData (Q₁.toSubSystem.twist Q₂.toSubSystem) hxy
      (Q₁'.toSubSystem.twist Q₂'.toSubSystem) r

def NefRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (M : LineBundle k x) (M' : LineBundle k y) (r : Ω → K'),
      RestrictData M.toSubSystem hxy M'.toSubSystem r → Nef M.toSubSystem → Nef M'.toSubSystem

def StepData.JProper.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ f ∉ primeOf (S := k) x

def SubvarDrop.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (d : ℕ) (pp : Ideal (Poly k N)), IsSubvar x (primeOf (S := k) x) (d + 1) → pp.IsPrime →
    (∀ p ∈ pp, ∀ n : ℕ, homogeneousComponent n p ∈ pp) → primeOf (S := k) x ≤ pp →
    (∃ j, (X j : Poly k N) ∉ pp) → (∃ f ∈ pp, f ∉ primeOf (S := k) x) → ∃ e ≤ d, IsSubvar x pp e

def StepTwo.Reduce.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M₁ M₂ : FinGradedSub (S := S) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
    ∀ J : Ideal (Poly S N), (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) →
    ∃ (n : ℕ) (pr : Fin n → Ideal (Poly S N)) (sh : Fin n → ℤ),
      (∀ i, (pr i).IsPrime ∧ (∀ p ∈ pr i, ∀ d : ℕ, homogeneousComponent d p ∈ pr i) ∧
        primeOf (S := S) x ≤ pr i ∧
        ∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ pr i) ∧
      ∀ (Q : LineBundle S x) (c : ℤ),
        (∀ i, (∃ j, (X j : Poly S N) ∉ pr i) →
          Subsingleton (SubSystem.quotH (Q.twist (twistSys S x (c + sh i)))
            ((Q.twist (twistSys S x (c + sh i))).twist (idealSys x (pr i))) 1)) →
        Subsingleton (SubSystem.quotH ((M₁.tildeSys 0).twist (Q.twist (twistSys S x c)))
          ((M₂.tildeSys 0).twist (Q.twist (twistSys S x c))) 1)

section Hypotheses

variable (k : Type u) [Field k]

def pt01 : Fin (1 + 1) → k := fun i => if i = 0 then 0 else 1

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman

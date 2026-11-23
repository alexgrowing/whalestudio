import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

open Classical in

def eBeta {R : Type} [CommRing R] {ι : Type} {r : ℕ} (LL : Letters ι) (S : Set ι) {k1 : Type} [CommRing k1]
    (j : R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1) :
    MvPolynomial (ι × Fin r) R →+* MvPolynomial (ι × Fin r) k1 :=
  eval₂Hom (C.comp j) fun v =>
    if v.1 ∈ S then
      (if LL.vec v.1 then ∑ a : Fin r, C (g0inv a v.2) * X (v.1, a)
       else ∑ a : Fin r, C (g0 v.2 a) * X (v.1, a))
    else X v

open Classical in

def eWt {ι : Type} {r : ℕ} [NeZero r] (LL : Letters ι) (S : Set ι) (m : ι × Fin r →₀ ℕ) : ℤ :=
  m.sum fun v k => if v.2 = lastIdx r ∧ v.1 ∈ S then (if LL.vec v.1 then (k : ℤ) else -(k : ℤ)) else 0

def HSupp : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (k1 : Type) [CommRing k1] (j : R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1), g0 * g0inv = 1 →
    ∀ (G : MvPolynomial (ι × Fin r) R) (th : ℤ), (th : WithTop ℤ) ≤ valS LL S G →
      ∀ m ∈ (eBeta LL S j g0 g0inv G).support, th ≤ eWt LL S m

def matA (R : Type) [CommRing R] {ι : Type} {r : ℕ} (A : Fin r → ι) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  Matrix.of fun i j : Fin r => (X (A i, j) : MvPolynomial (ι × Fin r) R)

def HCop : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) (r : ℕ) [NeZero r] (A : Fin r → ι), Function.Injective A →
    (matA R A).adjugate (lastIdx r) (lastIdx r) ≠ 0 ∧
    IsRelPrime (detA (R := R) A) ((matA R A).adjugate (lastIdx r) (lastIdx r))

def E1 : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (A : Fin r → ι), Function.Injective A → (∀ l, A l ∈ S ∧ LL.vec (A l) = true) →
    (∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R), G ∈ Pol R r d →
      ∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → (degOther LL S A d : ℤ) < th →
        (detA (R := R) A) ^ (th - degOther LL S A d).toNat ∣ G)

end Formalism.MainNotions.G.GLWeightTheory

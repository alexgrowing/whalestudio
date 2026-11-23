import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def stdSymp (g : ℕ) (i j : Fin (2 * g)) : ℤ :=
  if (i : ℕ) < g ∧ (j : ℕ) = (i : ℕ) + g then 1
  else if (j : ℕ) < g ∧ (i : ℕ) = (j : ℕ) + g then -1 else 0

variable {S : Scheme.{0}}

abbrev baseOver (S : Scheme.{0}) : Over S := Over.mk (𝟙 S)

def linComb {A : Over S} [GrpObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    T ⟶ A :=
  (List.ofFn fun i => y i ^ a i).prod

structure Level (P : PolAV S) (k : ℕ) (ze : Γ(S, ⊤)ˣ) where

  pt : Fin (2 * P.g) → (baseOver S ⟶ P.A)

  prim : IsPrimitiveRoot ze k

  torsion : ∀ i, pt i ^ k = 1

  indep : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (c c' : Fin (2 * P.g) → Fin k),
    linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) =
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c' i : ℕ)) →
    c = c'

  span : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : Over.mk s ⟶ P.A), y ^ k = 1 →
    ∃ c : Fin (2 * P.g) → Fin k,
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) = y

  pairing : ∀ i j, WeilIs P.A P.L k (pt i) (pt j) (ze ^ stdSymp P.g i j)

def Level.toPt {P : PolAV S} {k : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P k ze)
    (a : Fin (2 * P.g) → ZMod k) : baseOver S ⟶ P.A :=
  linComb lev.pt (fun i => (a i).val)

end ReciprocityTheory.ChartRestriction.G.Out

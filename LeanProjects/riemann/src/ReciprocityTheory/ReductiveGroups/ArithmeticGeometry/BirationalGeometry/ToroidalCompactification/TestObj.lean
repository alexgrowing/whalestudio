import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma tensor_punit_eq_zero (x : ℝ ⊗[ℤ] PUnit.{1}) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul r u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

instance : Subsingleton (ℝ ⊗[ℤ] PUnit.{1}) :=
  ⟨fun a b => by rw [tensor_punit_eq_zero a, tensor_punit_eq_zero b]⟩

def zeroDatum (H : Host E) : Datum H where
  La := PUnit
  fin := inferInstance
  proj := inferInstance
  EF := 0
  alt _ := rfl
  unimod := ⟨fun _ _ _ => Subsingleton.elim _ _, fun f => ⟨PUnit.unit, LinearMap.ext fun x => by
    have : x = 0 := Subsingleton.elim _ _
    subst this
    exact (map_zero f).symm⟩⟩
  adj _ _ _ := rfl
  p := 0
  q := 0
  rank := Module.finrank_zero_of_subsingleton
  dom := ⟨0, fun _ => Subsingleton.elim _ _, fun _ _ => by simp, fun x hx => absurd (Subsingleton.elim x 0) hx,
    fun a A t _ ht => by
      have hA : A = 0 := LinearMap.ext fun _ => Subsingleton.elim _ _
      subst hA
      simp [ht]⟩

example (H : Host E) : (zeroDatum H).p * (zeroDatum H).q = 0 := rfl

def trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

lemma trivLB_isLB (X : Scheme.{0}) : (trivLB X).IsLB where
  cover := by simp [trivLB]
  g_self _ := map_one _
  cocycle _ _ _ := by
    show res _ 1 * res _ 1 = res _ 1
    rw [map_one, map_one, map_one, _root_.one_mul]

example (H : Host E) (l : Level H) : l.GoodAt 1 ↔ 3 ≤ l.M := by
  simp [Level.GoodAt, Nat.factorization_eq_zero_of_not_prime _ Nat.not_prime_one]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test

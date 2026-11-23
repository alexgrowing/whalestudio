import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair

noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X]

abbrev Kap.M1 := W1 n x.A X k.g x.a

abbrev Kap.EpsilonEtaTensorDual := pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a

def Kap.b1 (v : F.Vl) : AddSubgroup (k.M1 X) where
  carrier := {Z | ∀ i j, j < i → (k.wi1 X v * (Z : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j = 0}
  add_mem' h h' i j e := by
    rw [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, h i j e, h' i j e, add_zero]
  zero_mem' i j _ := by simp
  neg_mem' h i j e := by
    rw [Submodule.coe_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, h i j e, neg_zero]

def Kap.Zb (v : F.Vl) : AddSubgroup (F.Gv v → k.M1 X) where
  carrier := {β | IsLocallyConstant β ∧
    (∀ g h, (β (g * h) : Matrix (Fin n) (Fin n) (DD X k.g)) =
      β g + k.ρ1 X (F.φ v g) * β h * k.ρ1 X (F.φ v g)⁻¹) ∧ (∀ g, β g ∈ k.b1 X v) ∧
    ∀ g ∈ F.mu v, ∀ i, (k.wi1 X v * (β g : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i i = 0}
  add_mem' := by
    rintro β β' ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun g h => ?_, fun g => add_mem (a3 g) (b3 g), fun g hg i => ?_⟩
    · simp only [Pi.add_apply, Submodule.coe_add, a2, b2, Matrix.mul_add, Matrix.add_mul]; abel
    · rw [Pi.add_apply, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, a4 g hg, b4 g hg, add_zero]
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp, fun g => zero_mem _, fun g _ i => by simp⟩
  neg_mem' := by
    rintro β ⟨a1, a2, a3, a4⟩
    refine ⟨a1.comp Neg.neg, fun g h => ?_, fun g => neg_mem (a3 g), fun g hg i => ?_⟩
    · simp only [Pi.neg_apply, Submodule.coe_neg, a2, Matrix.mul_neg, Matrix.neg_mul]; abel
    · rw [Pi.neg_apply, Submodule.coe_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, a4 g hg, neg_zero]

def TyPat {X : Type} [CommRing X] {g : ℕ} (ty : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) (DD X g)) : Prop :=
  ∀ i j, (Z i j).ep' = 0 ∧ (Z i j).eta = 0 ∧ (ty i = ty j → (Z i j).ep = 0) ∧ (ty i ≠ ty j → (Z i j).a = 0)

end UpperTheory.V.Pa

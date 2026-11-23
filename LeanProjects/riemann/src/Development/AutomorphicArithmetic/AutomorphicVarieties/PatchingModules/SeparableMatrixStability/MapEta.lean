import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels

noncomputable section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

def DD.map {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (g : ℕ) (f : X →ₐ[A] X') :
    DD X g →ₐ[A] DD X' g where
  toFun x := ⟨f x.a, fun j => f (x.ep j), fun j => f (x.ep' j), f x.eta⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  commutes' a := by
    show _ = DD.C (algebraMap A X' a)
    have : algebraMap A (DD X g) a = DD.C (algebraMap A X a) := rfl
    rw [this]
    ext <;> simp

section

variable {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (g : ℕ) (f : X →ₐ[A] X')
  (x : DD X g)

@[simp] theorem DD.map_a : (DD.map g f x).a = f x.a := rfl
@[simp] theorem DD.map_ep (j) : (DD.map g f x).ep j = f (x.ep j) := rfl
@[simp] theorem DD.map_ep' (j) : (DD.map g f x).ep' j = f (x.ep' j) := rfl
@[simp] theorem DD.map_eta : (DD.map g f x).eta = f x.eta := rfl

instance [Finite X] : Finite (DD X g) := Finite.of_equiv _ (DD.equiv (X := X) (g := g)).symm

end

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)

abbrev NP.redD (g m : ℕ) : DD x.A g →ₐ[x.A] DD (x.Am m) g := DD.map g (Ideal.Quotient.mkₐ x.A _)

def NP.UnipOn (H : Subgroup F.Γ) : Prop :=
  ∀ (m : ℕ) (h : F.G₀), (h : F.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (mat x.ρ (h ^ l ^ e) - 1) i j ∈ Ideal.span {x.t ^ m}

end UpperTheory.V.Pa

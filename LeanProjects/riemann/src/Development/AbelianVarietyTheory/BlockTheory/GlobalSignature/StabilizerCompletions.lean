import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts

open scoped TensorProduct Pointwise
open NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

def UnramifiedAtFinite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def IsSelfDualLattice (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin M → E)) = ⊤ ∧
    ∀ y : Fin M → E, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (hE σ J x y)

def perpPart (L : Set (Fin M → E)) (x : Fin M → E) : Set (Fin M → E) :=
  {y | y ∈ L ∧ hE σ J x y = 0}

def actVec (k : HA (Af F) σ J) (y : Fin M → Af F ⊗[F] E) : Fin M → Af F ⊗[F] E :=
  ((HA.mat (Af F) σ J k : GL (Fin M) (Af F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec y

def ratVec (F : Type) [Field F] [NumberField F] [Algebra F E] (x : Fin M → E) :
    Fin M → Af F ⊗[F] E := fun i => inclR (Af F) (x i)

omit [NumberField E] in
theorem actVec_one (y : Fin M → Af F ⊗[F] E) : actVec σ J 1 y = y := by
  show ((1 : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec y = y
  simp

omit [NumberField E] in
theorem actVec_mul (g k : HA (Af F) σ J) (y : Fin M → Af F ⊗[F] E) :
    actVec σ J (g * k) y = actVec σ J g (actVec σ J k y) := by
  show (((HA.mat (Af F) σ J g) * (HA.mat (Af F) σ J k) : GL (Fin M) (Af F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _).mulVec y = _
  unfold actVec
  rw [Units.val_mul, Matrix.mulVec_mulVec]

def stabHat (L : Set (Fin M → E)) : Subgroup (HA (Af F) σ J) where
  carrier := {k | ∀ y, y ∈ latHat F E L ↔ actVec σ J k y ∈ latHat F E L}
  one_mem' := by intro y; rw [actVec_one]
  mul_mem' := by
    intro a b ha hb y
    rw [actVec_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (actVec σ J g⁻¹ y)
    rw [← actVec_mul, mul_inv_cancel, actVec_one] at this
    exact this.symm

abbrev stabVec (x : Fin M → E) : Subgroup (HA (Af F) σ J) := Hstab (Af F) σ J (fun _ => x)

def OrbitClaims (L : Set (Fin M → E)) (x : Fin M → E) (β : F) : Prop :=
  (∀ y ∈ latHat F E L, qR (Af F) σ J y = algebraMap F (Af F) β →
    ∃ k ∈ stabHat σ J L, actVec σ J k (ratVec F x) = y) ∧
  {h : HA (Af F) σ J | actVec σ J h⁻¹ (ratVec F x) ∈ latHat F E L} =
    (stabVec σ J x : Set (HA (Af F) σ J)) * (stabHat σ J L : Set (HA (Af F) σ J)) ∧
  stabHat σ J L ⊓ stabVec σ J x = stabHat σ J (perpPart σ J L x) ⊓ stabVec σ J x

end Lattice

def StabTransitive : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLattice σ J L →
    ∀ (β : F), (β = 1 ∨ β = -1) →
    ∀ x ∈ L, hE σ J x x = algebraMap F E β →
      OrbitClaims σ J (L : Set (Fin M → E)) x β

section Basic₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

omit [NumberField E] in

theorem mem_stabVec (x : Fin M → E) (k : HA (Af F) σ J) :
    k ∈ stabVec σ J x ↔ actVec σ J k (ratVec F x) = ratVec F x := by
  constructor
  · intro h
    exact congrFun (MulAction.mem_stabilizer_iff.1 h) 0
  · intro h
    exact MulAction.mem_stabilizer_iff.2 (funext fun _ => h)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts

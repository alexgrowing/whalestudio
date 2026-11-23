import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwist
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Linear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory TopologicalSpace MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

def IsCoherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
  F.IsQuasicoherent ∧ ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)

abbrev algebraOfOver (X : Scheme.{u}) (A : Type u) [CommRing A] [X.Over (Spec (.of A))] :
    Algebra A Γ(X, ⊤) :=
  overAlgebra (CommRingCat.of A)

namespace ProjSpace

variable (A : Type u) [CommRing A] (n : ℕ)

def toSpecBase : projectiveSpace A n ⟶ Spec (.of A) :=
  Proj.toSpecZero (grading A n) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (grading A n 0)))

instance overSpec : (projectiveSpace A n).Over (Spec (.of A)) := ⟨toSpecBase A n⟩

variable {A n}

def twist (G : (projectiveSpace A n).Modules) (k : ℤ) : (projectiveSpace A n).Modules :=
  G ⊗ twistingSheaf (grading A n) k

end ProjSpace

namespace ProjScheme

variable {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}} (i : X ⟶ projectiveSpace A n)

def twistingSheaf (k : ℤ) : X.Modules :=
  (Scheme.Modules.pullback i).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)

def twist (F : X.Modules) (k : ℤ) : X.Modules :=
  F ⊗ twistingSheaf i k

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh

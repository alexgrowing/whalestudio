import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

noncomputable section

open scoped TensorProduct Quaternion

namespace GlobalTheory.QSA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def nrm {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def coords {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : Fin 4 → R :=
  ![x.re, x.imI, x.imJ, x.imK]

scoped instance top {R : Type*} [CommRing R] [TopologicalSpace R] {a b : R} : TopologicalSpace ℍ[R, a, b] :=
  TopologicalSpace.induced coords inferInstance

variable (F : Type) [Field F] [NumberField F]

abbrev DA (a b : F) : Type := ℍ[AF F, algebraMap F (AF F) a, algebraMap F (AF F) b]

variable {F}

def rat {a b : F} (x : ℍ[F, a, b]) : DA F a b :=
  ⟨algebraMap F (AF F) x.re, algebraMap F (AF F) x.imI, algebraMap F (AF F) x.imJ, algebraMap F (AF F) x.imK⟩

def H0 {a b : F} (ε : AF F) : Set (DA F a b) :=
  {x | ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ x = rat γ * h}

theorem nrm_mul {R : Type*} [CommRing R] {a b : R} (x y : ℍ[R, a, b]) : nrm (x * y) = nrm x * nrm y := by
  simp only [nrm, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem mul_star_eq {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : x * star x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem nrm_rat {a b : F} (x : ℍ[F, a, b]) : nrm (rat x) = algebraMap F (AF F) (nrm x) := by
  simp [nrm, rat]

theorem one_mem_H0_weight_zero {a b : F} (ε : AF F) : (1 : DA F a b) ∈ H0 ε :=
  ⟨1, by simp [nrm], 1, by simp [nrm], by simp, by ext <;> simp [rat]⟩

end GlobalTheory.QSA

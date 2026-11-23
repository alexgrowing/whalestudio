import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.NontrivialTransvection
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Plane
open GlobalTheory.UTrans.Model

def ext2 {E : Type} [CommRing E] {n : ℕ} (U : Matrix (Fin n) (Fin 2) E) (V : Matrix (Fin 2) (Fin n) E)
    (N : Matrix (Fin 2) (Fin 2) E) : Matrix (Fin n) (Fin n) E := 1 + U * (N - 1) * V

variable {E : Type} [Field E] {n : ℕ}

def cols (z w : Fin n → E) : Matrix (Fin n) (Fin 2) E := Matrix.of fun a i => ![z a, w a] i

def what₂ (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (z w : Fin n → E) : Matrix (Fin 2) (Fin n) E :=
  Matrix.of fun i b => ![∑ e, G b e * σ (w e), ∑ e, G b e * σ (z e)] i

end GlobalTheory.UTrans.Plane

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.QhtUnip

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

open Classical in
variable (E : Type) [Field E] [NumberField E] [Algebra F E] in

def bddA (S : Finset (Pl F)) (c : ℝ≥0) : Set (AE F E) :=
  {z | (∀ v : Pl F, absFin F v (compFin F E v z) ≤ if v ∈ S then c else 1) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), ‖infEmb τ (compInf F E w z)‖₊ ≤ c}

variable (F) (E : Type) [Field E] [NumberField E] [Algebra F E] in

def Bdd (ι : Type) : Set (ι → AE F E) := {f | ∃ (S : Finset (Pl F)) (c : ℝ≥0), ∀ t, f t ∈ bddA E S c}

abbrev Ix (m : ℕ) : Type := (Fin 1 ⊕ Fin m) ⊕ Fin 1

def ixE (m : ℕ) : Fin (m + 2) ≃ Ix m :=
  (finCongr (by omega : m + 2 = (1 + m) + 1)).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin 1))))

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

def basP {m : ℕ} (H : Plane E (m + 2) m) : Matrix (Fin (m + 2)) (Ix m) E :=
  fun r i => Sum.elim (Sum.elim (fun _ => H.x r) (fun k => H.ι r k)) (fun _ => H.y r) i

def basQ {m : ℕ} (H : Plane E (m + 2) m) : Matrix (Fin (m + 2)) (Fin (m + 2)) E := (basP H).submatrix id (ixE m)

def crd {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin (m + 2)) (Fin (m + 2)) E} (H : Plane E (m + 2) m) (g : UA σ J) :
    Matrix (Ix m) (Ix m) (AE F E) :=
  ((incM F (basQ H))⁻¹ * mat g * incM F (basQ H)).submatrix (ixE m).symm (ixE m).symm

def Heisenberg₂ {R : Type} [CommRing R] {m : ℕ} (a w : Fin m → R) (α : R) : Matrix (Ix m) (Ix m) R :=
  Matrix.fromBlocks (Matrix.fromBlocks 1 (Matrix.of fun _ k => a k) 0 1)
    (Matrix.of fun i _ => Sum.elim (fun _ => α) w i) 0 1

def gI {R : Type} [CommRing R] {m : ℕ} (J₁ : Matrix (Fin m) (Fin m) R) : Matrix (Ix m) (Ix m) R :=
  Matrix.fromBlocks (Matrix.fromBlocks 0 0 0 J₁) (Matrix.of fun i _ => Sum.elim (fun _ => 1) 0 i)
    (Matrix.of fun _ j => Sum.elim (fun _ => -1) 0 j) 0

example (S : Finset (Pl F)) (c : ℝ≥0) : (0 : AE F E) ∈ bddA E S c :=
  ⟨fun v => by simp, fun w τ => by simp⟩

theorem heis_zero {R : Type} [CommRing R] {m : ℕ} : Heisenberg₂ (0 : Fin m → R) 0 0 = 1 := by
  ext ((i | i) | i) ((j | j) | j) <;> simp [Heisenberg₂, Matrix.one_apply, Matrix.fromBlocks]

end GlobalTheory.QhtUnip

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.Folding

theorem inUJ_inv_left {m : ℕ} {ε : Fin m → Bool} {M : Mat m} (hM : M ∈ UJset ε) :
    (Jm ε * Mᴴ * Jm ε) * M = 1 := by
  have h : Mᴴ * Jm ε * M = Jm ε := hM
  calc Jm ε * Mᴴ * Jm ε * M = Jm ε * (Mᴴ * Jm ε * M) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Jm_mul_self]

theorem inUJ_inv_right {m : ℕ} {ε : Fin m → Bool} {M : Mat m} (hM : M ∈ UJset ε) :
    M * (Jm ε * Mᴴ * Jm ε) = 1 := mul_eq_one_comm.mp (inUJ_inv_left hM)

def mk {m : ℕ} {ε : Fin m → Bool} (M : Mat m) (hM : M ∈ UJset ε) : UJ ε :=
  ⟨⟨M, Jm ε * Mᴴ * Jm ε, inUJ_inv_right hM, inUJ_inv_left hM⟩, hM⟩

theorem umat_mem {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : umat g ∈ UJset ε := g.2

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

end Frob

theorem continuous_umat {m : ℕ} {ε : Fin m → Bool} : Continuous (umat : UJ ε → Mat m) :=
  Units.continuous_val.comp continuous_subtype_val

variable {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}

def iota (hmem : ∀ h ∈ UJset ε', embH e h ∈ UJset ε) (hmul : ∀ h h', embH e (h * h') = embH e h * embH e h') :
    UJ ε' →* UJ ε where
  toFun h := mk (embH e (umat h)) (hmem _ (umat_mem h))
  map_one' := by
    apply Subtype.ext; apply Units.ext
    exact embH_one e
  map_mul' h h' := by
    apply Subtype.ext; apply Units.ext
    exact hmul _ _

end GlobalTheory.SepReal.Folding

namespace GlobalTheory.SepReal.Folding

variable {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}

end GlobalTheory.SepReal.Folding

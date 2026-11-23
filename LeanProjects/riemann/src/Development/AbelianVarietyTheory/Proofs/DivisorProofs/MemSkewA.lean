import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.ResidueEisenstein.ModConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def skewA (σ : E →ₐ[F] E) (j : ℕ) : AddSubgroup (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) where
  carrier := {c | c + cT (sigR (AF F) σ) c = 0}
  add_mem' := fun {a b} ha hb => by
    have e : cT (sigR (AF F) σ) (a + b) = cT (sigR (AF F) σ) a + cT (sigR (AF F) σ) b :=
      Matrix.ext fun i k => by simp [cT]
    change a + b + cT _ (a + b) = 0
    change a + cT _ a = 0 at ha
    change b + cT _ b = 0 at hb
    rw [e, add_add_add_comm, ha, hb, add_zero]
  zero_mem' := by
    change (0 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + cT _ 0 = 0
    ext i k; simp [cT]
  neg_mem' := fun {a} ha => by
    have e : cT (sigR (AF F) σ) (-a) = -cT (sigR (AF F) σ) a := Matrix.ext fun i k => by simp [cT]
    change -a + cT _ (-a) = 0
    change a + cT _ a = 0 at ha
    rw [e, ← neg_add, ha, neg_zero]

theorem mem_skewA {σ : E →ₐ[F] E} {j : ℕ} {c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)} :
    c ∈ skewA σ j ↔ c + cT (sigR (AF F) σ) c = 0 := Iff.rfl

example (σ : E →ₐ[F] E) : (Matrix.of ![![0, 1], ![-1, 0]] : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) ∈ skewA σ 2 := by
  rw [mem_skewA]
  ext i k; fin_cases i <;> fin_cases k <;> simp [cT]

end GlobalTheory.ResidueEisenstein.ModConj

end

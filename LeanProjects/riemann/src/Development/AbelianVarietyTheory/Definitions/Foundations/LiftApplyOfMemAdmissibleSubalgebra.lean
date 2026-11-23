import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def admissibleLettersSubalgebra (R : Type) [CommRing R] (N l : ℕ) : Subalgebra R (FreeAlgebra R Letter) :=
  Algebra.adjoin R (FreeAlgebra.ι R '' {T | admitted N l T})

def SSPotB (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ admissibleLettersSubalgebra ℂ N l, FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.SSBB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (lam : Letter → E) :
    Prop :=
  ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, admitted N l T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

theorem iota_mem_admissibleSubalgebra (R : Type) [CommRing R] {N l : ℕ} {T : Letter} (hT : admitted N l T) :
    FreeAlgebra.ι R T ∈ admissibleLettersSubalgebra R N l :=
  Algebra.subset_adjoin ⟨T, hT, rfl⟩

theorem lift_apply_of_mem_admissibleSubalgebra {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {N l : ℕ}
    {f : Letter → Module.End R M} {lam : Letter → R} {x : M} (hx : ∀ T, admitted N l T → f T x = lam T • x)
    {P : FreeAlgebra R Letter} (hP : P ∈ admissibleLettersSubalgebra R N l) :
    FreeAlgebra.lift R f P x = FreeAlgebra.lift R lam P • x := by
  have := SSAdm.lift_sub_smul_mem (A := {T | admitted N l T}) (W := ⊥) (f := f) (lam := lam) (x := x)
    (fun T _ z hz => by rw [(Submodule.mem_bot R).1 hz, map_zero]; exact Submodule.zero_mem _)
    (fun T hT => (Submodule.mem_bot R).2 (sub_eq_zero.2 (hx T hT))) hP
  exact sub_eq_zero.1 ((Submodule.mem_bot R).1 this)

theorem SSPotB_iff_SSPotA {N l w : ℕ} {lam : Letter → ℂ} : SSPotB N l w lam ↔ SSPotA N l w lam := Iff.rfl

theorem Tower.SSBB_iff_SSBA (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]
    {lam : Letter → E} : X.SSBB N l w E lam ↔ X.SSBA N l w E lam := Iff.rfl

example (N l : ℕ) : FreeAlgebra.ι ℂ Letter.U ∈ admissibleLettersSubalgebra ℂ N l := iota_mem_admissibleSubalgebra ℂ trivial

example (N l : ℕ) : FreeAlgebra.ι ℂ (Letter.T 1) ∉ admissibleLettersSubalgebra ℂ N l := by
  classical
  intro h
  have := SSAdm.lift_congr (A := {T | admitted N l T}) (B := ℂ) (f := fun _ => 0)
    (g := fun T => if admitted N l T then 0 else 1) (fun T hT => (if_pos hT).symm) h
  have hn : ¬ admitted N l (Letter.T 1) := fun h => Nat.not_prime_one h.1
  simp [hn] at this

end GlobalTheory.KZ

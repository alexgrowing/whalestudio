import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

noncomputable section

namespace GlobalTheory.PackLoc

def embOpt {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (h : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => h i j
    | none, none => 1
    | _, _ => 0

def embOptL {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (X : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => X i j
    | _, _ => 0

theorem embH_eq_embOpt {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (h : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embH e h = embOpt e h := rfl

theorem embL_eq_embOptL {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (X : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embL e X = embOptL e X := rfl

theorem embOpt_one {m N : ℕ} (e : Option (Fin m) ≃ Fin N) : embOpt e 1 = 1 := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Matrix.one_apply]

end GlobalTheory.PackLoc

end

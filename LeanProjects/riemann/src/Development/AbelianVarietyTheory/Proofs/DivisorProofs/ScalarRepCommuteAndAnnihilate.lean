import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem action_commute_and_killed_by_polynomials
    (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ)
    (R : Type) [CommRing R] [Algebra R Λ] (φ : R →+* O)
    (ρ : Λ →+* Matrix (Fin h) (Fin h) O)
    (hρ : ∀ c : R, ρ (algebraMap R Λ c) = φ c • (1 : Matrix (Fin h) (Fin h) O)) :
    (∀ a b : Λ, Commute (Matrix.toLin' ((ρ a).map (algebraMap O C)))
      (Matrix.toLin' ((ρ b).map (algebraMap O C)))) ∧
    ∀ (a : Λ) (f : Polynomial R), Polynomial.aeval a f = 0 →
      Polynomial.aeval (Matrix.toLin' ((ρ a).map (algebraMap O C)))
        (f.map ((algebraMap O C).comp φ)) = 0 := by
  let Φ : Λ →+* Module.End C (Fin h → C) :=
    ((Matrix.toLinAlgEquiv' (R := C) (n := Fin h)).toRingEquiv.toRingHom).comp
      (((algebraMap O C).mapMatrix).comp ρ)
  have hΦ : ∀ a, Matrix.toLin' ((ρ a).map (algebraMap O C)) = Φ a := fun a => by
    ext i j
    simp [Φ, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
  have hscal : (algebraMap C (Module.End C (Fin h → C))).comp ((algebraMap O C).comp φ)
      = Φ.comp (algebraMap R Λ) := by
    ext c : 1
    show _ = Φ (algebraMap R Λ c)
    rw [RingHom.comp_apply, ← hΦ, hρ]
    ext i j
    simp [Matrix.toLin'_apply, Matrix.one_apply, Pi.single_apply, Module.algebraMap_end_apply,
      Matrix.map_apply, Matrix.mulVec]
    split_ifs <;> simp
  refine ⟨fun a b => ?_, fun a f hf => ?_⟩
  · rw [hΦ, hΦ]
    exact (Commute.all a b).map Φ
  · rw [hΦ, Polynomial.aeval_def, Polynomial.eval₂_map, hscal, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, hf, map_zero]

end GlobalTheory

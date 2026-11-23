import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

noncomputable section

namespace GlobalTheory.HermitianFormLinearity

open NumberField

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem hform_add_left (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (x + x') y =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (y + y') =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (c • x) y =
      starRingEnd E c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (c • y) =
      c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_zero_left (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem hform_zero_right (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x 0 = 0 := by
  simp [Formalism.UG.hform]

theorem hform_span_eq_zero (J : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (hS : ∀ y ∈ S, ∀ z ∈ S, Formalism.UG.hform (starRingEnd E) J y z = 0) :
    ∀ x ∈ Submodule.span E S, ∀ y ∈ Submodule.span E S,
      Formalism.UG.hform (starRingEnd E) J x y = 0 := by
  have h1 : ∀ x ∈ S, ∀ y ∈ Submodule.span E S, Formalism.UG.hform (starRingEnd E) J x y = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hS x hx z hz
    | zero => exact hform_zero_right J x
    | add a b _ _ ha hb => rw [hform_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [hform_smul_right, ha, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem z hz => exact h1 z hz y hy
  | zero => exact hform_zero_left J y
  | add a b _ _ ha hb => rw [hform_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [hform_smul_left, ha, mul_zero]

theorem main : ∀ (I : Formalism.MainNotions.S.AutInst)
    (R : Submodule (NumberField.RingOfIntegers (Formalism.MainNotions.S.AutInst.E I))
      (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I)),
    R ≠ ⊥ →
    (∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd (Formalism.MainNotions.S.AutInst.E I)) (Formalism.MainNotions.S.AutInst.J I) y z
      = (0 : Formalism.MainNotions.S.AutInst.E I)) →
    Formalism.MainNotions.S.AutInst.IsIsot I (Submodule.span (Formalism.MainNotions.S.AutInst.E I)
      (↑R : Set (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I))) := by
  intro I R hR hiso
  refine ⟨?_, hform_span_eq_zero I.J _ hiso⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  intro h
  apply hr0
  have : r ∈ Submodule.span I.E (↑R : Set (Fin I.n → I.E)) := Submodule.subset_span hr
  rw [h] at this
  exact (Submodule.mem_bot _).1 this

end GlobalTheory.HermitianFormLinearity

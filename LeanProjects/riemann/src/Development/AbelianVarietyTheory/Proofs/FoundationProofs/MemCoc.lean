import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.InertCoh

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def cob (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v}
  zero_mem' := ⟨0, fun s _ => by simp⟩
  add_mem' := by
    rintro a b ⟨v, hv⟩ ⟨w, hw⟩
    refine ⟨v + w, fun s hs => ?_⟩
    simp only [Pi.add_apply, hv s hs, hw s hs, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨v, hv⟩
    refine ⟨k • v, fun s hs => ?_⟩
    simp only [Pi.smul_apply, hv s hs, Matrix.mulVec_smul, smul_sub]

def coc (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
    ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t}
  zero_mem' := ⟨fun i => continuous_const, fun s i => c.O.zero_mem, fun s _ t _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun i => (ha1 i).add (hb1 i), fun s i => c.O.add_mem (ha2 s i) (hb2 s i), fun s hs t ht => ?_⟩
    simp only [Pi.add_apply, ha3 s hs t ht, hb3 s hs t ht, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨ha1, ha2, ha3⟩
    refine ⟨fun i => ?_, fun s i => ?_, fun s hs t ht => ?_⟩
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact continuous_const.mul (ha1 i)
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact c.O.mul_mem k.2 (ha2 s i)
    · simp only [Pi.smul_apply, ha3 s hs t ht, Matrix.mulVec_smul, smul_add]

theorem mem_cob {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ cob W c I ↔ ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v := Iff.rfl

theorem mem_coc {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ coc W c I ↔ (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
      ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t := Iff.rfl

end GlobalTheory.InertCoh

end

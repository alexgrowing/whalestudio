import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

theorem shCoc_wsum_props : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
  (ρ : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin 2) (Fin 2) (Qbar l)) (cf : Coef l) (ι : Type) [Fintype ι] (cw : ι → Qbar l)
  (Yx : ι → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ i r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Yx i r)) →
  (∀ i r, Yx i r = push (redL l r) (Yx i (r + 1))) →
  (∀ i r y j, Continuous fun s => Yx i r s y j) →
  (∀ i r s u j, Yx i r s u j ∈ cf.O) → (∀ i, cw i ∈ cf.O) →
  (∀ r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (fun s y => ∑ i, cw i • Yx i r s y)) ∧
  (∀ r, (fun s y => ∑ i, cw i • Yx i r s y) = push (redL l r) (fun s y => ∑ i, cw i • Yx i (r + 1) s y)) ∧
  (∀ r y j, Continuous fun s => (∑ i, cw i • Yx i r s y) j) ∧
  (∀ r s u j, (∑ i, cw i • Yx i r s u) j ∈ cf.O) := by
  intro l _ Ω _ _ ρ cf ι _ cw Yx hC hP hCont hO hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s t x
    have := fun i => hC i r s t x
    simp only [this, Finset.sum_add_distrib, smul_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
  · intro r
    funext s y
    simp only [push]
    conv_lhs => rw [show (∑ i, cw i • Yx i r s y) = ∑ i, cw i • push (redL l r) (Yx i (r + 1)) s y from by
      simp only [← hP]]
    simp only [push, Finset.smul_sum]
    exact Finset.sum_comm
  · intro r y j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (hCont i r y j)
  · intro r s u j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hw i) (hO i r s u j)

end GlobalTheory.K4

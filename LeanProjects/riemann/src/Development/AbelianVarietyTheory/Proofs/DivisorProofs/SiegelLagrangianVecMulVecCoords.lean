import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SiegelConv

theorem vecOf_single_basis (F : Type) [Field F] {E : Type} [Field E] [Algebra F E] [Module.Finite F E] {n : ℕ}
    (j : Fin n) (i : Fin (Module.finrank F E)) :
    vecOf F (Pi.single (j, i) (1 : F)) = Pi.single j (Module.finBasis F E i) := by
  funext j'
  simp only [vecOf]
  by_cases h : j' = j
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  · rw [Pi.single_eq_of_ne h]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Pi.single_apply, h]

theorem De_vecMulVec_basisMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (De : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F))
    (D : Matrix (Fin d) (Fin n ⊕ Fin n) E →ₗ[F] (κ → F) × (κ → F)), (∀ u, De (incM F u) = GlobalTheory.SiegelConv.ratP (D u)) →
    ∀ (w : Fin d → E) (t : Fin n × Fin (Module.finrank F E) → AF F),
      De (Matrix.vecMulVec (incV F w) (Sum.elim (GlobalTheory.SiegelConv.basisMap F E n t) (GlobalTheory.SiegelConv.basisMap F E n t))) =
        GlobalTheory.SiegelConv.extA (D ∘ₗ GlobalTheory.SiegelConv.vvMap F (n := n) w) t := by
  intro F E _ _ _ _ _ n d κ _ De D hD w t
  have key : Matrix.vecMulVec (incV F w) (Sum.elim (basisMap F E n t) (basisMap F E n t)) =
      ∑ k, t k • incM F (vvMap F (n := n) w (Pi.single k 1)) := by
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, incM, Matrix.map_apply, vvMap, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.vecMulVec_apply, incV]
    rw [Fintype.sum_prod_type]
    rcases b with j' | j' <;>
    · simp only [Sum.elim_inl, Sum.elim_inr, vecOf_single_basis, basisMap, Finset.mul_sum]
      rw [Finset.sum_eq_single j']
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.single_eq_same, map_mul, mul_smul_comm]
      · intro b _ hb
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Pi.single_eq_of_ne (Ne.symm hb)]; simp
      · simp
  rw [key, map_sum]
  simp only [map_smul, hD, extA, LinearMap.coe_comp, Function.comp_apply]

end GlobalTheory.SiegelConv

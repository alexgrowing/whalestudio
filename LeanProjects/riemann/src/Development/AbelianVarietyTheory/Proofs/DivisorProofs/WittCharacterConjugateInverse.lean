import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.chrX_conj_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ z : (AE F E)ˣ, χX (Units.map (cA σ).toMonoidHom z) = (χX z)⁻¹ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h z
  have hcm := h.base.cm
  set a : (AF F)ˣ := Units.map (Algebra.norm (AF F) (S := AE F E)) z with ha
  have h1 := h.resX a
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, ha.symm⟩))] at h1
  have h2 : χX (Units.map ↑(algebraMap (AF F) (AE F E)) a) = 1 := by
    ext; simpa using h1
  have h3 : (Units.map ↑(algebraMap (AF F) (AE F E)) a) = z * Units.map (cA σ).toMonoidHom z := by
    ext
    simp only [ha, Units.coe_map, MonoidHom.coe_coe, Units.val_mul]
    exact GlobalTheory.Doubling.algebraMap_norm_eq hcm (R := AF F) (z : AE F E)
  rw [h3, map_mul] at h2
  exact eq_inv_of_mul_eq_one_right h2

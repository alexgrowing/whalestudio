import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem continuous_of_frameCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (X : Type) [TopologicalSpace X] (f : X → GAd σ J), Continuous (fun x => (matHom _ σ J (f x)).1 * adMat F C) → Continuous (fun x => (matHom _ σ J (f x)).1 * adMat F Z) → Continuous (fun x => (matHom _ σ J (f x)).1 * adMat F D) → Continuous f := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF X _ f hC hZ hD
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J))
      + adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    simp only [adMat, ← Matrix.map_mul]
    rw [← Matrix.map_add _ (map_add _), ← Matrix.map_add _ (map_add _), hF.sum]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hval : Continuous fun x => (matHom _ σ J (f x)).1 := by
    have e : ∀ x, (matHom _ σ J (f x)).1 = (matHom _ σ J (f x)).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J)
        + (matHom _ σ J (f x)).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J))
        + (matHom _ σ J (f x)).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
      intro x
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.mul_add, hs, Matrix.mul_one]
    refine Continuous.congr ?_ fun x => (e x).symm
    exact ((hC.matrix_mul continuous_const).add (hZ.matrix_mul continuous_const)).add (hD.matrix_mul continuous_const)
  have hcont : Continuous (adjA σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose).matrix_mul continuous_const
  have hinv : Continuous fun x => ((matHom _ σ J (f x))⁻¹).1 := by
    have e : ∀ x, ((matHom _ σ J (f x))⁻¹).1 = adjA σ J (matHom _ σ J (f x)).1 := fun x => by
      rw [adjA_mat hF.herm, map_inv]
    exact (hcont.comp hval).congr fun x => (e x).symm
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨hval, hinv⟩)

end GlobalTheory.SphEis

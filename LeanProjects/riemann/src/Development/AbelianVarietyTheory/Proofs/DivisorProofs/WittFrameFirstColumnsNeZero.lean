import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvApply
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open GlobalTheory.PoleFactor

noncomputable section

namespace GlobalTheory.PoleFactor

open GlobalTheory.SiegelSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_completion_tensor_pos {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (w : InfinitePlace F)
    (hr : w.IsReal) (y : w.Completion ⊗[F] E) :
    0 ≤ InfinitePlace.Completion.ringEquivRealOfIsReal hr (Algebra.norm w.Completion y) ∧
      (y ≠ 0 → 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hr (Algebra.norm w.Completion y)) := by
  obtain ⟨τ⟩ := nonempty_embOver F (E := E) w
  let ι := RingEquiv.ofBijective (infEmb τ) (infEmb_bijective hcm τ)
  set φ := InfinitePlace.Completion.ringEquivRealOfIsReal hr
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι y) two_pos
  have hy : y = (ι.symm z) ^ 2 := by
    apply ι.injective
    rw [map_pow, RingEquiv.apply_symm_apply, hz]
  have hnn : 0 ≤ φ (Algebra.norm w.Completion y) := by
    rw [hy, map_pow, map_pow]
    exact sq_nonneg _
  refine ⟨hnn, fun hy0 => lt_of_le_of_ne hnn (Ne.symm ?_)⟩
  have hu : IsUnit y := by
    have hne : ι y ≠ 0 := fun h => hy0 (ι.injective (by rw [h, map_zero]))
    have h1 : IsUnit (ι y) := Ne.isUnit hne
    simpa using h1.map ι.symm
  have h2 : Algebra.norm w.Completion y ≠ 0 := (hu.map (Algebra.norm w.Completion)).ne_zero
  exact (map_ne_zero φ).2 h2

end GlobalTheory.PoleFactor

end

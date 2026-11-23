import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxAdaptedPlaneEvaluation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfCom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK

theorem exists_unit_at_evI_piInf_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (τ : ∀ w : InfinitePlace F, EmbOver E w) (β : InfinitePlace F → ℂ), IsCMExt F E σ → (∀ w, β w ≠ 0) → ∃ t : (AE F E)ˣ, At (evI F) (t.1 - 1) ∧ ∀ w, piInf (τ w) t.1 = β w := by
  intro F E _ _ _ _ _ σ τ β hCM hβ
  obtain ⟨z, hz, hzw⟩ := exists_at_evI_piInf_eq F E σ hCM τ (fun w => β w - 1)
  obtain ⟨z', hz', hzw'⟩ := exists_at_evI_piInf_eq F E σ hCM τ (fun w => (β w)⁻¹ - 1)
  have hs : At (evI F) (z + z' + z * z') := by
    intro u hu
    rw [smul_add, smul_add, ← smul_mul_assoc, hz u hu, hz' u hu, zero_mul, add_zero, add_zero]
  have h1 : (1 + z) * (1 + z') = 1 := by
    have h0 : z + z' + z * z' = 0 := by
      refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM τ _ hs fun w => ?_
      rw [map_add, map_add, map_mul, hzw, hzw']
      have := hβ w
      field_simp
      ring
    linear_combination h0
  refine ⟨Units.mkOfMulEqOne (1 + z) (1 + z') h1, ?_, fun w => ?_⟩
  · simpa using hz
  · simp [Units.val_mkOfMulEqOne, map_add, hzw]

end GlobalTheory.ThK

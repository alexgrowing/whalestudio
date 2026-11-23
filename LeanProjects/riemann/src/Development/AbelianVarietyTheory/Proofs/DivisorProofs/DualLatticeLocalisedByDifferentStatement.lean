import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeLocalisedByDifferent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_localised_by_different : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), J.det ≠ 0 → L.IsLattice E →
    (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (δ : E) (s : 𝓞 F), δ ≠ 0 → s ∉ v.asIdeal →
    (∀ t : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * t))) → IsIntegral ℤ (δ * t)) →
    (∀ t : E, IsIntegral ℤ (δ * t) → ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * (algebraMap F E (s : F) * t)))) →
    IsSelfDualAt σ (δ • Jᵀ) L v := by
  first | exact @GlobalTheory.TraceSelfDualAt.isSelfDualAt_smul_transpose | exact GlobalTheory.TraceSelfDualAt.isSelfDualAt_smul_transpose | (intros; apply GlobalTheory.TraceSelfDualAt.isSelfDualAt_smul_transpose <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CMNormSum

theorem algebraMap_norm_and_inj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (w : InfinitePlace F) :
    (∀ t : w.Completion ⊗[F] E,
      algebraMap w.Completion (w.Completion ⊗[F] E) (Algebra.norm w.Completion t) = sigR w.Completion σ t * t) ∧
    Function.Injective (algebraMap w.Completion (w.Completion ⊗[F] E)) := by
  have := h.1
  have hr : w.IsReal := IsTotallyReal.isReal w
  let e : w.Completion ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal hr
  have he : ∀ a, InfinitePlace.Completion.extensionEmbedding w a = ((e a : ℝ) : ℂ) :=
    fun a => (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr a).symm
  obtain ⟨τ⟩ := (inferInstance : Nonempty (GlobalTheory.AdelicU.EmbOver E w))
  let φ := GlobalTheory.AdelicU.infEmb τ
  have hbij := GlobalTheory.AdelicU.infEmb_bijective h τ
  have hφa : ∀ a : w.Completion, φ (algebraMap w.Completion (w.Completion ⊗[F] E) a) = ((e a : ℝ) : ℂ) := by
    intro a
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    show GlobalTheory.AdelicU.infEmb τ (a ⊗ₜ[F] (1 : E)) = _
    rw [GlobalTheory.AdelicU.infEmb_tmul, map_one, mul_one, he]
  have hinj : Function.Injective (algebraMap w.Completion (w.Completion ⊗[F] E)) := by
    intro a b hab
    have := congrArg φ hab
    rw [hφa, hφa] at this
    exact e.injective (Complex.ofReal_injective this)
  refine ⟨fun t => ?_, hinj⟩
  let e₂ : w.Completion ⊗[F] E ≃+* ℂ := RingEquiv.ofBijective φ hbij
  have hN : Algebra.norm w.Completion t = e.symm (Algebra.norm ℝ (e₂ t)) := by
    refine Algebra.norm_eq_of_equiv_equiv e e₂ ?_ t
    ext a
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [show e₂ (algebraMap w.Completion (w.Completion ⊗[F] E) a) = φ (algebraMap _ _ a) from rfl, hφa]
    rfl
  apply hbij.1
  rw [hφa, hN, e.apply_symm_apply, Algebra.norm_complex_apply, map_mul,
    ← GlobalTheory.AdelicU.infEmb_sigR h τ t]
  show ((Complex.normSq (φ t) : ℝ) : ℂ) = starRingEnd ℂ (φ t) * φ t
  rw [Complex.normSq_eq_conj_mul_self]

theorem sum_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (w : InfinitePlace F) (k k' : ℕ) (z : Fin k → w.Completion ⊗[F] E) (z' : Fin k' → w.Completion ⊗[F] E),
    ∑ i, sigR w.Completion σ (z i) * z i = ∑ i, sigR w.Completion σ (z' i) * z' i →
    ∑ i, Algebra.norm w.Completion (z i) = ∑ i, Algebra.norm w.Completion (z' i) := by
  intro F E _ _ _ _ _ σ h w k k' z z' hz
  obtain ⟨hN, hinj⟩ := algebraMap_norm_and_inj F E σ h w
  apply hinj
  rw [map_sum, map_sum]
  simp only [hN]
  exact hz

end GlobalTheory.CMNormSum

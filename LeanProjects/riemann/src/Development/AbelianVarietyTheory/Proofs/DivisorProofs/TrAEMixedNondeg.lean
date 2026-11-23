import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ArchSch

theorem trAE_mixed_nondeg (F : Type) [Field F] [NumberField F] (ξ : mixedEmbedding.mixedSpace F)
    (h : ∀ η : mixedEmbedding.mixedSpace F, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (ξ * η) = 0) : ξ = 0 := by
  classical
  let η : mixedEmbedding.mixedSpace F := (fun i => (ξ.1 i)⁻¹, fun i => (ξ.2 i)⁻¹)
  have h1 : ξ * η * ξ = ξ := by
    ext i
    · by_cases hi : ξ.1 i = 0 <;> simp [η, hi]
    · by_cases hi : ξ.2 i = 0 <;> simp [η, hi]
  have h2 : IsIdempotentElem (Algebra.lmul ℝ (mixedEmbedding.mixedSpace F) (ξ * η)) := by
    unfold IsIdempotentElem
    rw [← map_mul, ← mul_assoc, h1]
  have h3 := h η
  rw [Algebra.trace_apply] at h3
  have h4 : Algebra.lmul ℝ (mixedEmbedding.mixedSpace F) (ξ * η) = 0 := by
    have hp := (LinearMap.IsIdempotentElem.isProj_range _ h2).trace
    rw [h3] at hp
    have h5 : Module.finrank ℝ (LinearMap.range (Algebra.lmul ℝ (mixedEmbedding.mixedSpace F) (ξ * η))) = 0 := by
      exact_mod_cast hp.symm
    exact LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 h5)
  have h6 := LinearMap.congr_fun h4 ξ
  rw [← h1]
  simpa using h6

theorem trAE_eq_zero (F : Type) [Field F] [NumberField F] (a : AF F) (ha : ∀ u : AF F, evI F u = 0 → u * a = 0)
    (h : evI F a = 0) : a = 0 := by
  have h1 : a.1 = 0 := by
    unfold evI at h
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 h
  have h2 : a.2 = 0 := by
    have h3 := ha (((0 : Ainf F), (1 : Af F)) : Ainf F × Af F) (by unfold evI; exact map_zero _)
    have h4 : (1 : Af F) * a.2 = 0 := congrArg Prod.snd h3
    rwa [one_mul] at h4
  exact Prod.ext h1 h2

theorem trAE_evI_mul (F : Type) [Field F] [NumberField F] (a b : AF F) : evI F (a * b) = evI F a * evI F b := by
  unfold evI
  exact map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem trAE_evI_liftA (F : Type) [Field F] [NumberField F] (ξ : mixedEmbedding.mixedSpace F) :
    evI F (liftA F ξ) = ξ :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply ξ

theorem trAE_mul_liftA (F : Type) [Field F] [NumberField F] (ξ : mixedEmbedding.mixedSpace F) (u : AF F)
    (hu : evI F u = 0) : u * liftA F ξ = 0 := by
  have h1 : u.1 = 0 := by
    unfold evI at hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

theorem trAE_trace_dual {F E A ι : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] [CommRing A] [Algebra F A] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (β : A ⊗[F] E) (j : ι) :
    Algebra.trace A (A ⊗[F] E) (β * (1 ⊗ₜ[F] b.traceDual j)) = (Algebra.TensorProduct.basis A b).repr β j := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis A b).sum_repr β]
  rw [Finset.sum_mul, map_sum]
  have key : ∀ i, Algebra.trace A (A ⊗[F] E) ((Algebra.TensorProduct.basis A b) i * (1 ⊗ₜ[F] b.traceDual j)) =
      if i = j then 1 else 0 := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.trace_apply,
      ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply, b.trace_mul_traceDual]
    split_ifs <;> simp
  simp only [smul_mul_assoc, map_smul, key, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem trAE_nondeg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (β : AE F E)
    (hβ : At (evI F) β)
    (h : ∀ t : AE F E, At (evI F) t →
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) (β * t))) = 0) : β = 0 := by
  classical
  let b := Module.finBasis F E
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  rw [map_zero]
  ext1 j
  rw [Finsupp.zero_apply]
  apply trAE_eq_zero
  · intro u hu
    have h1 := congrArg (fun z => (Algebra.TensorProduct.basis (AF F) b).repr z j) (hβ u hu)
    simpa using h1
  · apply trAE_mixed_nondeg
    intro η
    have h2 := h (liftA F η • ((1 : AF F) ⊗ₜ[F] b.traceDual j)) (by
      intro u hu
      rw [smul_smul, trAE_mul_liftA F η u hu, zero_smul])
    rw [mul_smul_comm, map_smul, trAE_trace_dual, smul_eq_mul, trAE_evI_mul, trAE_evI_liftA, mul_comm] at h2
    exact h2

end GlobalTheory.ArchSch

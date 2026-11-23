import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor

noncomputable section

namespace GlobalTheory.Eis.Conv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.AdelicU

theorem norm_halfE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    Algebra.norm (AF F) (halfE F E).1 = (halfInf F).1 ^ 2 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w).toRingHom.domain_nontrivial
  change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1) = _
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h]

theorem evFin_halfInf (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evFin F v (halfInf F).1 = 1 :=
  map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)

theorem evInf_halfInf (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    evInf F w (halfInf F).1 = algebraMap F _ 2⁻¹ :=
  (GlobalTheory.AutFunCompare.evW w).commutes _

theorem nnnorm_evInf_halfInf (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    ‖evInf F w (halfInf F).1‖₊ = 2⁻¹ := by
  rw [evInf_halfInf]
  have h2 : w (2⁻¹ : F) = 2⁻¹ := by
    rw [← InfinitePlace.norm_embedding_eq w, map_inv₀, norm_inv, map_ofNat]
    simp
  have e : ‖((2⁻¹ : F) : w.Completion)‖ = 2⁻¹ := (InfinitePlace.Completion.norm_coe w _).trans h2
  apply NNReal.eq
  rw [NNReal.coe_inv, NNReal.coe_ofNat]
  exact e

theorem absE_halfE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) : absE F E (halfE F E) = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := by
  haveI := h.1
  have hn := norm_halfE F E h.2.2.1
  have hfin : ∀ v, absEv F E v (unitFin F E v (halfE F E)) = 1 := fun v => by
    rw [absEv_unitFin, hn, map_pow, evFin_halfInf]
    simp
  have hinf : ∀ w, absEw F E w (unitInf F E w (halfE F E)) = 4⁻¹ := fun w => by
    rw [absEw_unitInf, hn, map_pow, nnnorm_pow, nnnorm_evInf_halfInf, InfinitePlace.mult,
      if_pos (IsTotallyReal.isReal w), pow_one, inv_pow]
    norm_num
  rw [absE_apply, finprod_eq_one_of_forall_eq_one hfin, mul_one, Finset.prod_congr rfl fun w _ => hinf w,
    Finset.prod_const, Finset.card_univ, inv_pow]

end GlobalTheory.Eis.Conv

end

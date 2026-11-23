import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CMSkewUnit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cm_sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cm_exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  haveI : IsTotallyComplex E := h.2.1
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)
  by_contra hne
  push_neg at hne
  apply hc
  ext x
  have hx := h.2.2.2 w.embedding x
  rw [hne x] at hx
  simpa [ComplexEmbedding.conjugate_coe_eq] using hx.symm

theorem cm_exists_skew (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨x, hx⟩ := cm_exists_moved σ h
  refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  rw [map_sub, cm_sigma_sigma σ h]; ring

end GlobalTheory.CMSkewUnit

namespace GlobalTheory.CMSkewUnit

theorem exists_unit_of_val_eq_one {F : Type} [Field F] [NumberField F] {v : Pl F} {x : Fv F v} (hx : Valued.v x = 1) :
    ∃ u : (v.adicCompletionIntegers F)ˣ, ((u : v.adicCompletionIntegers F) : Fv F v) = x := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hx; exact zero_ne_one hx
  have hmem : x ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_eq hx)
  have hmem' : x⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hx, inv_one])
  refine ⟨⟨⟨x, hmem⟩, ⟨x⁻¹, hmem'⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

end GlobalTheory.CMSkewUnit

namespace GlobalTheory.CMSkewUnit

theorem exists_skew_unit_at : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F) (π : AE F E →+* Fv F v),
    (∀ a : AF F, π (algebraMap (AF F) (AE F E) a) = evFin F v a) →
    ∃ δ : E, σ δ = -δ ∧ ∃ u : (v.adicCompletionIntegers F)ˣ,
      ((u : v.adicCompletionIntegers F) : Fv F v) = π (inclR (F := F) (AF F) δ) := by
  intro F E _ _ _ _ _ σ h v π hπ
  obtain ⟨δ₀, h0, hs⟩ := cm_exists_skew σ h
  have ht : π (inclR (F := F) (AF F) δ₀) ≠ 0 :=
    (map_ne_zero_iff (π.comp (inclR (F := F) (AF F))) (RingHom.injective _)).2 h0
  have hF : ∀ f : F, π (inclR (F := F) (AF F) (algebraMap F E f)) = algebraMap F (Fv F v) f := by
    intro f
    have e1 : inclR (F := F) (AF F) (algebraMap F E f) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) f) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes f
    rw [e1, hπ, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  set t := π (inclR (F := F) (AF F) δ₀) with ht_def
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  refine ⟨algebraMap F E (ϖ ^ WithZero.log (Valued.v t)) * δ₀, ?_, ?_⟩
  · rw [map_mul, AlgHom.commutes, hs]; ring
  · apply exists_unit_of_val_eq_one
    rw [map_mul, map_mul, hF, ← ht_def, map_mul]
    have e2 : Valued.v (algebraMap F (Fv F v) (ϖ ^ WithZero.log (Valued.v t))) =
        v.valuation F (ϖ ^ WithZero.log (Valued.v t)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [e2, map_zpow₀, hϖ]
    conv_lhs => rw [← WithZero.exp_log hvt]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp

end GlobalTheory.CMSkewUnit

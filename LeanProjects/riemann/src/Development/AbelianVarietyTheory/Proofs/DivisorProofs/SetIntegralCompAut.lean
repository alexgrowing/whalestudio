import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IncMDblR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.DiagThetaRatF

open MeasureTheory

theorem setIntegral_comp_aut {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [Countable Γ] {K : Set G} (hK : IsCompact K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) (ν : Measure G)
    [ν.IsAddHaarMeasure] {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (e : G ≃+ G) (he : Continuous e)
    (he' : Continuous e.symm) (hΓ : ∀ x ∈ Γ, e x ∈ Γ) (hΓ' : ∀ x ∈ Γ, e.symm x ∈ Γ) (φ : G → ℂ)
    (hφ : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) : ∫ x in 𝓕, φ (e x) ∂ν = ∫ x in 𝓕, φ x ∂ν := by
  let h : G ≃ₜ G := .mk e.toEquiv he he'
  let m : G ≃ᵐ G := h.toMeasurableEquiv
  haveI : (ν.map e).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν e he he'
  have hmp : MeasurePreserving m ν (ν.map e) := ⟨he.measurable, rfl⟩
  have hT : IsAddFundamentalDomain Γ (m.symm ⁻¹' 𝓕) (ν.map e) := by
    refine h𝓕.preimage_of_equiv hmp.symm.quasiMeasurePreserving (e := fun γ : Γ => (⟨e γ, hΓ _ γ.2⟩ : Γ)) ⟨?_, ?_⟩ ?_
    · intro a b hab
      exact Subtype.ext (e.injective (congrArg Subtype.val hab))
    · intro a
      exact ⟨⟨e.symm a, hΓ' _ a.2⟩, Subtype.ext (e.apply_symm_apply _)⟩
    · intro γ x
      show e.symm (e γ + x) = γ + e.symm x
      rw [map_add, e.symm_apply_apply]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
  have hac : ν.map e ≪ ν := hc ▸ Measure.smul_absolutelyContinuous
  have hF' : IsAddFundamentalDomain Γ 𝓕 (ν.map e) := h𝓕.mono hac
  have hpre : m ⁻¹' (m.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  have h0 : ν 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  have h1 : ν 𝓕 ≠ ⊤ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov ν h𝓕).ne
  have e1 : ν.map e (m.symm ⁻¹' 𝓕) = ν 𝓕 := by
    have := m.map_apply (μ := ν) (m.symm ⁻¹' 𝓕)
    rw [hpre] at this
    exact this
  have hc1 : (c : ENNReal) = 1 := by
    have e2 := hT.measure_eq hF'
    rw [e1, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e2
    exact ((ENNReal.mul_left_inj h0 h1).1 ((one_mul _).trans e2)).symm
  have hν : ν.map e = ν := by
    rw [hc, ENNReal.coe_eq_one.1 hc1, one_smul]
  have e3 := hmp.setIntegral_preimage_emb m.measurableEmbedding φ (m.symm ⁻¹' 𝓕)
  rw [hpre] at e3
  refine e3.trans ?_
  rw [hT.setIntegral_eq hF' fun g x => hφ g g.2 x, hν]

section Mat

variable {R : Type} [CommRing R] {m n : ℕ}

end Mat

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem det_ne_zero_of_unit {n : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (g₀ : Matrix (Fin n) (Fin n) E)
    (h : g.1 = incM F g₀) : g₀.det ≠ 0 := fun h0 => by
  haveI : Nontrivial (AF F ⊗[F] E) := (inclR_injective (F := F) (E := E)).nontrivial
  have := (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, h] at this
  refine this ?_
  have e : (incM F g₀).det = inclR (F := F) (AF F) g₀.det := by
    rw [RingHom.map_det]; rfl
  rw [e, h0, map_zero]

variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

end Adelic

end GlobalTheory.DiagThetaRatF

end

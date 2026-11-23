import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HermUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ ξ : E, ξ ≠ 0 ∧ σ ξ = -ξ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  by_contra hne
  push_neg at hne
  have hid : ∀ x, σ x = x := by
    intro x
    by_contra hx
    refine hne (x - σ x) (sub_ne_zero.2 (Ne.symm hx)) ?_
    rw [map_sub, hσ]; ring
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hr : ComplexEmbedding.IsReal w.embedding := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    simpa [hid x, Complex.star_def] using (h.2.2.2 w.embedding x).symm
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w)) (InfinitePlace.isReal_iff.2 hr)

theorem isMulRightInvariant_of_isHerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ μ : Measure (UA σ X.J), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro F E _ _ _ _ _ σ B n X r s hB hX μ hμ
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  obtain ⟨δ, hδ, hσδ⟩ := exists_anti hB.cm
  have hJ : IsHermND σ (X.J.map σ) := GlobalTheory.UnitaryVol.isHermND_map hσ hX
  have heq : GlobalTheory.WeilM.UG (cA σ) (incM F X.J) = HR (AF F) σ (X.J.map σ) := by
    have h := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ one_ne_zero
    rw [one_smul] at h
    exact h
  let e : UA σ X.J ≃* HA (AF F) σ (X.J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (HA (AF F) σ (X.J.map σ)) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ (X.J.map σ)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF F) σ (X.J.map σ)))
  haveI : ContinuousMul (UA σ X.J) := ⟨by
    have h3 : (fun p : UA σ X.J × UA σ X.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  haveI : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he he'
  have hR : (μ.map e).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ hσ hδ hσδ hJ (μ.map e)
  have hem : Measurable e := he.measurable
  have hem' : Measurable e.symm := he'.measurable
  refine ⟨fun g => ?_⟩
  have hmg : Measurable fun y : HA (AF F) σ (X.J.map σ) => y * e g := (continuous_mul_right (e g)).measurable
  have h1 : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map hem' hem]
    have : (e.symm ∘ e : UA σ X.J → UA σ X.J) = id := funext fun x => e.symm_apply_apply x
    rw [this, Measure.map_id]
  have h2 : ((μ.map e).map (fun y => y * e g)).map e.symm = μ.map (· * g) := by
    rw [Measure.map_map hmg hem, Measure.map_map hem' (hmg.comp hem)]
    congr 1
  rw [← h2, hR.map_mul_right_eq_self (e g), h1]

end GlobalTheory.HermUnimod

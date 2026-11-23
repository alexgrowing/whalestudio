import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompact
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurable
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_hypOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    IsHermND σ (hypOne J) := by
  refine ⟨fun i j => ?_, fun h => ?_⟩
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => change σ 0 = 0; simp
      | succ j =>
        induction j using Fin.cases with
        | zero => change σ 1 = 1; simp
        | succ j => change σ 0 = 0; simp
    | succ i =>
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => change σ 1 = 1; simp
        | succ j =>
          induction j using Fin.cases with
          | zero => change σ 0 = 0; simp
          | succ j => change σ 0 = 0; simp
      | succ i =>
        induction j using Fin.cases with
        | zero => change σ 0 = 0; simp
        | succ j =>
          induction j using Fin.cases with
          | zero => change σ 0 = 0; simp
          | succ j => exact hJ.1 i j
  · obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have hrow : ∀ i, ∑ j, hypOne J i j * v j = 0 := fun i => congrFun hv0 i
    have h1 : v 1 = 0 := by
      have := hrow 0
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [hypOne_zero_rest, hypOne_zero_zero, hypOne_zero_one] using this
    have h0 : v 0 = 0 := by
      have := hrow 1
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [hypOne_one_rest, hypOne_one_zero, hypOne_one_one] using this
    have ht : J.mulVec (fun j : Fin M => v j.succ.succ) = 0 := by
      funext i
      have := hrow i.succ.succ
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at this
      simpa [Matrix.mulVec, dotProduct, hypOne_rest_rest, hypOne_rest_zero, hypOne_rest_one] using this
    have hz : (fun j : Fin M => v j.succ.succ) = 0 := by
      by_contra hne
      exact hJ.2 (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hne, ht⟩)
    apply hv
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i =>
      induction i using Fin.cases with
      | zero => exact h1
      | succ i => exact congrFun hz i

end Alg

theorem measurableSet_primV (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet (primV σ J b v) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  obtain ⟨-, -, -, t2, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := t2
  obtain ⟨-, lc, sc, -, -, hact⟩ := GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ (M + 2) (hypOne J)
    (isHermND_hypOne σ J hJ) (Fv F v)
  haveI := lc
  haveI := sc
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hσ 1 (M + 2) v
  have hc := (hact 1).1
  have hlat := (GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 (M + 2)).2.2.2.1 v
  have hclopen : IsClopen (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    ⟨hlat.1.isClosed, hlat.2⟩
  have hcl : IsClosed {g : HA (Fv F v) σ (hypOne J) | latStab σ (hypOne J) b v g} := by
    have hE : {g : HA (Fv F v) σ (hypOne J) | latStab σ (hypOne J) b v g} =
        ⋂ x : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E,
          {g | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} := by
      ext g
      simp [latStab]
    rw [hE]
    refine isClosed_iInter fun x => ?_
    have hcx : Continuous fun g : HA (Fv F v) σ (hypOne J) => actW (Fv F v) σ (hypOne J) g x :=
      hc.comp (continuous_id.prodMk continuous_const)
    have hp := hclopen.preimage hcx
    by_cases hx : x ∈ (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E))
    · have hs : {g : HA (Fv F v) σ (hypOne J) | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} =
          (fun g => actW (Fv F v) σ (hypOne J) g x) ⁻¹' latV b v := by
        ext g
        simp [hx]
      rw [hs]
      exact hp.1
    · have hs : {g : HA (Fv F v) σ (hypOne J) | actW (Fv F v) σ (hypOne J) g x ∈ latV b v ↔ x ∈ latV b v} =
          ((fun g => actW (Fv F v) σ (hypOne J) g x) ⁻¹' latV b v)ᶜ := by
        ext g
        simp [hx]
      rw [hs]
      exact hp.compl.1
  have hcont : Continuous fun g : HA (Fv F v) σ (hypOne J) => actW (Fv F v) σ (hypOne J) g (e0 _ M) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have him : IsSigmaCompact (primV σ J b v) := by
    exact (isSigmaCompact_univ.of_isClosed_subset hcl (Set.subset_univ _)).image hcont
  obtain ⟨K, hK, hU⟩ := him
  rw [← hU]
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

theorem measurable_purePr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → Measurable (purePr σ J b S Ψinf Ψ) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b S Ψinf Ψ hΨinf hΨ
  obtain ⟨hpi, hpf, hpv, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 (M + 2)
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_af F E σ hσ 1 (M + 2)
  haveI := GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_ainf F E σ hσ 1 (M + 2)
  haveI : ∀ v, BorelSpace (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
    fun v => GlobalTheory.CompanionTheory.SW.PureMeas.borelSpace_fv F E σ hσ 1 (M + 2) v
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hset : MeasurableSet {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
      ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} := by
    have hE : {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E |
        ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v} =
        ⋂ v, ⋂ _ : v ∉ S, (fun y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E => projV v (projFin y)) ⁻¹'
          primV σ J b v := by
      ext y
      simp
    rw [hE]
    refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
    exact ((hpv v).comp hpf).measurable (measurableSet_primV F E σ hσ M J hJ d b v)
  unfold purePr
  refine Measurable.indicator ?_ hset
  refine (hΨinf.comp hpi.measurable).mul ?_
  refine Finset.measurable_prod _ fun v _ => ?_
  exact (hΨ v).comp ((hpv v).comp hpf).measurable

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas

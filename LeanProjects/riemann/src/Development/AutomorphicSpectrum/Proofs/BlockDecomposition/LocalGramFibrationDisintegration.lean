import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProperStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocalStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv

theorem isFibreFamily_map_homeo {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y)
    (e : V ≃ₜ V) (hf : ∀ v, f (e v) = f v) (U : Set V) (hU : e ⁻¹' U = U) (hμ : μ.map e = μ)
    (B : Set X) (fib : X → Measure V) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B (fun b => (fib b).map e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  refine ⟨?_, ?_, ?_⟩
  · intro b
    have hset : e ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι b} ∩ U)ᶜ := by
      rw [Set.preimage_compl, Set.preimage_inter, hU]
      congr 2
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hf]
    show ((fib b).map e) _ = 0
    rw [hemb.map_apply, hset]
    exact h1 b
  · intro φ hφ
    have hr : μ.restrict U = (μ.restrict U).map e := by
      have := hemb.restrict_map μ U
      rw [hμ, hU] at this
      exact this
    rw [hr, hemb.lintegral_map, h2 (fun v => φ (e v)) (hφ.comp e.measurable)]
    refine lintegral_congr fun b => ?_
    simp only [hemb.lintegral_map]
  · intro φ hφ hcs hts
    have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport_comp_eq_preimage, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨hi, hcont⟩ := h3 (φ ∘ e) (hφ.comp e.continuous)
      (hcs.comp_isClosedEmbedding e.isClosedEmbedding) hts'
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [hemb.integrable_map_iff]
      exact hi b hb
    · have : (fun b => ∫ v, φ v ∂((fib b).map e)) = fun b => ∫ v, (φ ∘ e) v ∂(fib b) := by
        funext b
        exact hemb.integral_map φ
      rw [this]
      exact hcont

theorem linearIndependent_mulVec {K : Type} [CommRing K] {M n : ℕ} (g : GL (Fin M) K) (X : Fin n → Fin M → K)
    (hX : LinearIndependent K X) :
    LinearIndependent K (fun a => (g : Matrix (Fin M) (Fin M) K).mulVec (X a)) := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) := by
    intro x y hxy
    have h2 := congrArg (((g⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K).mulVec) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2
  exact hX.map' (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) (LinearMap.ker_eq_bot.2 hinj)

theorem map_actW_fibre_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm h S
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨_, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R
  obtain ⟨hcont, hone, hmul, hgr⟩ := hact n
  have hcg : ∀ k : HA R σ J, Continuous (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) := fun k =>
    hcont.comp (Continuous.prodMk_right k)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actW R σ J h
      invFun := actW R σ J h⁻¹
      left_inv := fun X => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun X => by rw [← hmul, mul_inv_cancel, hone]
      continuous_toFun := hcg h
      continuous_invFun := hcg h⁻¹ }
  let W : Set (Fin n → Fin M → R ⊗[F] E) := {X | LinearIndependent (R ⊗[F] E) X}
  have hWo : IsOpen W := GlobalTheory.T.linearly_independent_frames_open F E σ hσ R hR n M
  have hfree : ∀ (k : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), X ∈ W → actW R σ J k X ∈ W :=
    fun k X hX => linearIndependent_mulVec (HA.mat R σ J k) X hX
  have hU : e ⁻¹' W = W := by
    ext X
    refine ⟨fun hX => ?_, hfree h X⟩
    have h2 : actW R σ J h⁻¹ (actW R σ J h X) ∈ W := hfree h⁻¹ _ hX
    have h3 : actW R σ J h⁻¹ (actW R σ J h X) = X := by rw [← hmul, inv_mul_cancel, hone]
    rw [h3] at h2
    exact h2
  have hμm : μ.map e = μ := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hσ M J hJ R hR n μ hμ h
  have ht := isFibreFamily_map_homeo μ ν (gramR R σ J) Subtype.val e (fun X => hgr h X) W hU hμm
    Set.univ m hm
  have hm0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' Set.univ ∩ W) ν Set.univ m := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact hm
  have ht0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' Set.univ ∩ W) ν Set.univ
      (fun b => (m b).map e) := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact ht
  exact GlobalTheory.T.measurable_embedding_of_injective_proper _ _ _ μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hgf W hWo Set.univ Set.univ
    isOpen_univ isOpen_univ subset_rfl m (fun b => (m b).map e) hm0 ht0 S (Set.mem_univ S)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv

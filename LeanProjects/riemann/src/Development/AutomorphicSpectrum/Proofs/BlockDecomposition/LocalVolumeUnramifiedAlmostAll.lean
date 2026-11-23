import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProperStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalMeasuresOrthogonalSumAlmostAllPlaces
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageGoodFree

theorem stage_good_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Fv F v) σ J n μ ν m → ∀ h : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m (hermOf (Fv F v) σ T hT) {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m (hermOf (Fv F v) σ T hT) (latV b v)) (actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [GoodTrans.good_trans F E σ hCM (M + 1) _ hND t ht d b,
    (LatRat.latV_rational F E σ hCM d b n M).2.2, (LatRat.latV_rational F E σ hCM d b 0 M).2.2]
    with v hv hv1 hv0
  intro μ ν m hμ hν hm h
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hBorel, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have := hBorel n M
  have hOpen := ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hND (Fv F v)
  obtain ⟨-, -, -, -, -, hactJ⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (Fv F v)
  obtain ⟨-, hone, hmul, hgram⟩ := hact 1
  by_cases he : actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) ∈ latV b v
  · rw [Set.indicator_of_mem he]
    have he0 : (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) ∈ latV b v := by
      have h0 := (hv0 (fun a : Fin 0 => a.elim0)).2 (fun a => a.elim0)
      have hc : consTup (fun a : Fin 0 => a.elim0) =
          (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) := by
        funext a
        exact Fin.cases rfl (fun j => j.elim0) a
      rwa [hc] at h0
    obtain ⟨k, hk, hkl⟩ := hv _ _ he0 he (StageGood.gram_first (Fv F v) σ J t) (hgram h _)
    obtain ⟨ι, -, -, hrange, -, hcons⟩ := StabFirst.stab_first F E σ hCM M J hJ t ht (Fv F v)
    have hg : actW (Fv F v) σ _ (k⁻¹ * h) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) =
        (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) := by
      rw [hmul, ← hk, ← hmul, inv_mul_cancel, hone]
    obtain ⟨u, hu⟩ := (hrange _).2 hg
    have hh : h = k * ι u := by rw [hu]; group
    have hset : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} =
        actW (Fv F v) σ J u ⁻¹' latV b v := by
      ext X
      rw [Set.mem_ofPred_eq, Set.mem_preimage, hh]
      have := (hact (n + 1)).2.2.1 k (ι u) (consTup X)
      rw [this, hkl, hcons, hv1]
    have hcont : Continuous (actW (Fv F v) σ J u : (Fin n → Fin M → Fv F v ⊗[F] E) → _) :=
      (hactJ n).1.comp (Continuous.prodMk continuous_const continuous_id)
    rw [hset, ← Measure.map_apply hcont.measurable hOpen.measurableSet,
      GlobalTheory.T.local_gram_fibration_disintegration F E σ hCM M J hJ (Fv F v) hLoc n μ ν m hμ hν hm u]
  · rw [Set.indicator_of_notMem he]
    have hempty : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hX => he (StageGood.first_mem b v σ _ h X hX)
    rw [hempty, measure_empty]

end GlobalTheory.CompanionTheory.SW.StageGoodFree

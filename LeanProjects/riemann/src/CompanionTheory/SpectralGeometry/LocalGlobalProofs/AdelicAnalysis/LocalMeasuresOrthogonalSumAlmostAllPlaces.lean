import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGram
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeGramScalarAlmostAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresInvariantStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageGood

theorem gram_first {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) :
    gramR R σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
  funext a c
  have h1 : (algebraMap F R t) ⊗ₜ[F] (1 : E) = (1 : R) ⊗ₜ[F] (algebraMap F E t) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  simp only [gramR, hR, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, map_one, map_zero,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, one_mul, mul_one, JR, Matrix.map_apply]
  show inclR R (blockOne (algebraMap F E t) J 0 0) = (algebraMap F R t) ⊗ₜ[F] (1 : E)
  rw [h1]
  rfl

theorem first_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (Fv F v) σ J)
    (X : Fin n → Fin M → Fv F v ⊗[F] E)
    (hX : actW (Fv F v) σ J h (consTup X) ∈ latV b v) :
    actW (Fv F v) σ J h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) ∈ latV b v := by
  intro a i k
  exact hX 0 i k

theorem stage_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Fv F v) σ J n μ ν m → ∀ h : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m (hermOf (Fv F v) σ T hT) {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m (hermOf (Fv F v) σ T hT) (latV b v)) (actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT _ d b
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
    obtain ⟨k, hk, hkl⟩ := hv _ _ he0 he (gram_first (Fv F v) σ J t) (hgram h _)
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
      GlobalTheory.T.gram_fiber_measures_invariant F E σ hCM M J hJ (Fv F v) hLoc n μ ν m hμ hν hm u]
  · rw [Set.indicator_of_notMem he]
    have hempty : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hX => he (first_mem b v σ _ h X hX)
    rw [hempty, measure_empty]

end GlobalTheory.CompanionTheory.SW.StageGood

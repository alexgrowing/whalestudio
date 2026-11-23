import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProperStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt

open GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale

theorem exists_scale_cover {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fin n → Fin M → Fv F v ⊗[F] E)) (hC : IsCompact C) :
    ∃ (c : F) (hc : c ≠ 0), C ⊆ latV (scaleB b c hc) v := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set p : Fv F v := algebraMap F (Fv F v) π with hp
  have hval : Valued.v p = WithZero.exp (-1 : ℤ) := by
    have h0 : Valued.v (algebraMap F (Fv F v) π) = v.valuation F π :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
    rw [hp, h0, hπ]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hlt : Valued.v p < 1 := by
    rw [hval]
    decide
  have hpO : p ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hlt.le
  have hnorm : ‖p‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 hlt
  have hlim : Filter.Tendsto (fun k : ℕ => p ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hOopen : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  have hmem : ∀ (k : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E),
      X ∈ latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v ↔
        ∀ a i l, p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          v.adicCompletionIntegers F := by
    intro k X
    simp only [latV, Set.mem_setOf_eq, repr_scaleB, map_pow, hp]
  let U : ℕ → Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun k => latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v
  have hUo : ∀ k, IsOpen (U k) := fun k =>
    (((GlobalTheory.T.adelic_tuple_projections F E σ hcm d (scaleB b (π ^ k) (pow_ne_zero k hπ0)) n M).2.2.2.1 v).2)
  have hcov : C ⊆ ⋃ k, U k := by
    intro X _
    have h1 : ∀ a i l, ∀ᶠ k : ℕ in Filter.atTop,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro a i l
      have h2 : Filter.Tendsto
          (fun k : ℕ => p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
          Filter.atTop (𝓝 0) := by
        simpa using hlim.mul_const ((Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
      exact h2 (hOopen.mem_nhds (zero_mem _))
    have h3 : ∀ᶠ k : ℕ in Filter.atTop, ∀ a i l,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i =>
        Filter.eventually_all.2 fun l => h1 a i l
    obtain ⟨k, hk⟩ := h3.exists
    exact Set.mem_iUnion.2 ⟨k, (hmem k X).2 hk⟩
  have hmono : Monotone U := monotone_nat_of_le_succ fun k X hX => by
    refine (hmem (k + 1) X).2 fun a i l => ?_
    have h := (hmem k X).1 hX a i l
    rw [pow_succ', mul_assoc]
    exact mul_mem hpO h
  obtain ⟨k, hk⟩ := hC.elim_directed_cover U hUo hcov hmono.directed_le
  exact ⟨π ^ k, pow_ne_zero k hπ0, hk⟩

theorem fibre_compact_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J T hT → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) m → ∀ C : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact C → m (hermOf (Fv F v) σ T hT) C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT hSW d b laminf lam hinf hv v m hm C hC
  classical
  obtain ⟨c, hc, hCc⟩ := exists_scale_cover σ hcm b n M v C hC
  set b' := scaleB b c hc with hb'
  have hrV : ∀ w, IsLocR (Fv F w) := GlobalTheory.T.completion_is_local_ring F
  haveI : ∀ w, BorelSpace (Fv F w) := fun _ => ⟨rfl⟩
  obtain ⟨k, hk0, hk⟩ := coord_rescale σ hcm J (Fv F v) (hrV v) b b' (lam v) (hv v).1 n m hm
  have hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hWi, hHi⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) _ b' laminf hinf.1
  obtain ⟨minf, hminf⟩ := GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hcm M n J hJ (coordW (Ainf F) b' laminf n M)
    (coordHerm (Ainf F) σ b' laminf n) (hWi n M) (hHi n)
  have hfV : ∀ w : HeightOneSpectrum (𝓞 F), ∃ fib : HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E),
      IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M) (coordHerm (Fv F w) σ b' (lam w) n) fib := fun w => by
    have := PI.VolStabS.secondCountable_Fv F w
    have := PI.VolStabS.locallyCompact_Fv F w
    obtain ⟨-, hWv, hHv⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F w) _ b' (lam w) (hv w).1
    exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J w n hcm hJ _ _ (hWv n M) (hHv n)
  choose m₀ hm₀ using hfV
  let m₂ : ∀ w : HeightOneSpectrum (𝓞 F), HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E) :=
    Function.update m₀ v (fun S => k • m S)
  have hm₂v : m₂ v = fun S => k • m S := Function.update_self _ _ _
  have hm₂ : ∀ w, IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M)
      (coordHerm (Fv F w) σ b' (lam w) n) (m₂ w) := fun w => by
    by_cases h : w = v
    · subst h
      rw [hm₂v]
      exact hk
    · have : m₂ w = m₀ w := Function.update_of_ne h _ _
      rw [this]
      exact hm₀ w
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁
  have hE := hSW d b' laminf lam hinf hv μ₁ 𝓕₁ hμ₁ h𝓕₁ minf m₂ hminf hm₂
  have h1 : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) < ⊤ := by
    have h2 : m₂ v (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := hE.1 v
    rwa [hm₂v] at h2
  have h3 : m (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := by
    by_contra hx
    have hs : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) =
        (k : ℝ≥0∞) * m (hermOf (Fv F v) σ T hT) (latV b' v) := by
      rw [Measure.smul_apply]
      rfl
    rw [hs, not_lt_top_iff.1 hx, ENNReal.mul_top (by exact_mod_cast hk0)] at h1
    exact lt_irrefl _ h1
  exact (measure_mono hCc).trans_lt h3

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCompactLowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCoverCountableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFreeFibreLocalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolumeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceGramUnitScalingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneVolumeBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDependentSetNullStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingCompactFreeSetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCompactCoverByUnitScalingsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalCompactCoverByUnitsStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.AvgZero

theorem avg_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U → |(coordW (Fv F v) b lam 1 M (A ∩ {X | algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal - (m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM h₀ d b v lam hlam m hm A hAc hAo
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, htr, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI : lam.IsAddHaarMeasure := hlam.1
  have hM1 : 1 ≤ M := by omega
  have hM2 : 2 ≤ M := by omega
  have hQ : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E =>
      algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) :=
    continuous_const.mul (htr.comp ((a10 1 M J).matrix_elem 0 0))
  have hfam := GlobalTheory.T.rank_one_free_fibre_local F E σ hCM M J hJ d b v lam hlam m hm
  have hnull := GlobalTheory.T.local_dependent_set_null F E σ hCM M J hJ hM1 d b v lam hlam
  obtain ⟨ι, hι, P, u, hPc, hPo, hPZ, hsum, hcov⟩ :
      ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ),
        IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧
        Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧
        A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆
          ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) =>
            (u i : Fv F v ⊗[F] E) * X p k) '' P := by
    by_cases hs : Nonempty (E →ₐ[F] Fv F v)
    · obtain ⟨τ⟩ := hs
      exact GlobalTheory.T.split_local_compact_cover_by_units F E σ hCM M hM2 v τ A hAc
    · exact GlobalTheory.T.local_compact_cover_by_unit_scalings F E σ hCM M hM2 v
        (GlobalTheory.CompanionTheory.DictLoc.isField_tensor_of_no_algHom hCM.2.2.1 (not_nonempty_iff.1 hs)) A hAc
  obtain ⟨c, hc⟩ := GlobalTheory.T.fibre_volume_compact_bound _ _ _ lam _ _ _ hQ hfam P hPc hPo hPZ
  have hset := fun i => GlobalTheory.T.unit_scaling_compact_free_set F E σ hCM M v (u i) P hPc hPo hPZ
  have hb := fun i S hS => GlobalTheory.T.local_rank_one_volume_bound F E σ hCM M J hJ hM1 d b v lam hlam P c hPo.measurableSet hc (u i) S hS
  have hmass := fun i => GlobalTheory.T.fibre_volume_compact_open_le_of_measure_le _ _ _ lam _ _ _ hQ hfam _ (hset i).1 (hset i).2.1 (hset i).2.2 _ (hb i)
  have key := GlobalTheory.T.fibre_volume_cover_countable _ _ ι _ lam _ _ _ hQ hfam hnull A hAc hAo _ _ hset hcov (hsum.mul_left c) hb hmass 0
  have e0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ = hermScal (Fv F v) σ 0 :=
    Subtype.ext (funext fun _ => funext fun _ => by
      show (1 : Fv F v) ⊗ₜ[F] (0 : E) = (0 : Fv F v) ⊗ₜ[F] (1 : E)
      simp)
  rw [e0]
  exact key

end GlobalTheory.CompanionTheory.SW.AvgZero

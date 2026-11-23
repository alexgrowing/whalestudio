import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoreR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBoxVolumeBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBoxIntegralSmallBallStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRankOneFreeOfPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRankOneVolumeBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationInjectiveOpenMapStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0

theorem fibre_rapid_zero_eq_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) (m : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) = ENNReal.ofReal (D (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM h₀ d b μ ν m hμ hν hm φ hφc hφ0 hφr D hDc hD
  obtain ⟨ρ, e, hρ, he, heρ, hen, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hCM.1
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis b
    simpa [hCM.2.2.1] using h.symm
  have hLoc : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hLoc
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hKr, hKl, hKs, hK2, -, -, -, hVb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hKr
  haveI := hKl
  haveI := hKs
  haveI := hK2
  haveI := hVb 1 M
  obtain ⟨hXl, hXs, hX2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) 1
  haveI := hXl
  haveI := hXs
  haveI := hX2
  haveI := hXb
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  have hreal : ∀ (A Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (Di : (InfinitePlace F → ℝ) → ℝ), Continuous Di → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∀ f : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by
    intro A Pm Di hDi hdens f hf hf0 hfr ε hε
    have hcard : Fintype.card (Fin M × Fin d) = M * 2 := by simp [hd]
    obtain ⟨C, hC⟩ := GlobalTheory.T.quadratic_box_volume_bound (InfinitePlace F) (Fin M × Fin d) A Pm Di (by omega) hDi hdens
    have hQ : Measurable (qR0 A : (InfinitePlace F → Fin M × Fin d → ℝ) → _) := by
      refine Continuous.measurable (continuous_pi fun w => continuous_const.mul ?_)
      exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
    exact GlobalTheory.T.quadratic_box_integral_small_ball (InfinitePlace F) (Fin M × Fin d) _ (by omega) (qR0 A) hQ C hC f hf hf0 hfr ε hε
  refine GlobalTheory.T.disintegration_injective_open_map _ _ _ μ ν (gramR (Ainf F) σ J) g Subtype.val Subtype.val_injective hgc hgf _ m (GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM (Ainf F) hLoc 1 M) hm φ hφc hφ0 D hDc hD ?_ _
  intro ε hε
  obtain ⟨δ, R, hδ, hR, hK, hb⟩ := GlobalTheory.T.archimedean_rank_one_volume_bound F E σ hCM M J hJ hM d b ρ e hρ he heρ hen hreal μ ν hμ hν φ hφc hφ0 hφr ε hε
  refine ⟨_, hK, ?_, hb⟩
  intro X hX
  refine GlobalTheory.T.archimedean_rank_one_free_of_places F E σ hCM M d b ρ e hρ he heρ X fun w h => ?_
  have h1 := (hX w).1
  have h2 : ‖(fun w => xw e b X w) w‖ = 0 := by
    show ‖xw e b X w‖ = 0
    rw [h, norm_zero]
  linarith

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0

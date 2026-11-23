import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompacts
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresTransitivityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNonunitsNull
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StdLat

theorem fibre_masses_standard_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ContinuousOn (fun s : Fv F v => (m (hermScal (Fv F v) σ s) (latV b v)).toReal) {0}ᶜ ∧
  ∫ s, (m (hermScal (Fv F v) σ s) (latV b v)).toReal ∂lam = 1 := by
  intro F E _ _ _ _ _ σ hCM J hJ d b v lam hlam m hm
  classical
  have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v) := hloc.1
  haveI : LocallyCompactSpace (Fv F v) := hloc.2.1
  haveI : SecondCountableTopology (Fv F v) := hloc.2.2.1
  haveI : T2Space (Fv F v) := hloc.2.2.2.1
  haveI := hlam.1
  obtain ⟨-, -, -, hT2K, -, htr, -, hBorW, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  haveI := hT2K
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b lam hlam.1
  obtain ⟨hLc, hLo, -, hL1⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b 1 2 v
  obtain ⟨hSh, -, hSm⟩ := GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hCM (Fv F v) d b
  haveI : BorelSpace (Fin 1 → Fin 2 → Fv F v ⊗[F] E) := hBorW 1 2
  haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
  have hLm : MeasurableSet (latV (M := 2) (n := 1) b v) := hLo.measurableSet
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin 1 → Fin 2 → Fv F v ⊗[F] E) → ℂ,
      φ = (latV b v).indicator (fun _ => (1 : ℂ)) := ⟨_, rfl⟩
  have hcl : IsClopen (latV (M := 2) (n := 1) b v) := ⟨hLc.isClosed, hLo⟩
  have hφc : Continuous φ := by
    rw [hφ]
    exact Continuous.indicator (fun a ha => by
      rw [hcl.frontier_eq] at ha; exact absurd ha (Set.notMem_empty a)) continuous_const
  have hφs : HasCompactSupport φ := by
    rw [hφ]
    exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨⟨hgc, -⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ hCM 2 J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m (hW 1 2) (hH 1) hm φ hφc hφs
  have hval : ∀ T, ∫ X, φ X ∂(m T) = (((m T (latV b v)).toReal : ℝ) : ℂ) := fun T => by
    rw [hφ, integral_indicator_const (1 : ℂ) hLm]
    simp [Measure.real]
  have hunit : ∀ z ∈ ({0}ᶜ : Set (Fv F v)),
      hermScal (Fv F v) σ z ∈
        {S : HermR (Fv F v) σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)).det} := by
    intro z hz
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    exact FibreRatio.isUnit_tmul (Fv F v) hz
  have hcont : ContinuousOn (fun z => (m (hermScal (Fv F v) σ z) (latV b v)).toReal) {0}ᶜ := by
    have h1 := hgc.comp hSh.continuous.continuousOn hunit
    have h2 := Complex.continuous_re.comp_continuousOn h1
    refine h2.congr fun z _ => ?_
    simp [hval]
  refine ⟨hcont, ?_⟩
  have hfin : ∀ S, m S (latV b v) < ⊤ := fun S => by
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM 2 J hJ (Fv F v) hloc 1 _ _ m (hW 1 2) (hH 1) hm S).1
    exact hLc.measure_lt_top
  obtain ⟨n1, n2⟩ := GlobalTheory.T.haar_measure_nonunits_null F E σ hCM 2 J hJ (by norm_num) v (coordW (Fv F v) b lam 1 2) lam (hW 1 2) hlam.1
  have n1' : lam ({0}ᶜ : Set (Fv F v))ᶜ = 0 := by
    refine measure_mono_null (fun c hc => ?_) n1
    have : c = 0 := by simpa using hc
    simp [this]
  have hres : lam.restrict ({0}ᶜ : Set (Fv F v)) = lam :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact n1')
  have hcq : Continuous fun X : Fin 1 → Fin 2 → Fv F v ⊗[F] E =>
      algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) :=
    continuous_const.mul (htr.comp ((hgr 1 2 J).matrix_elem 0 0))
  have hVm : MeasurableSet ({0}ᶜ : Set (Fv F v)) := (measurableSet_singleton 0).compl
  have hP : MeasurableSet {S | FibreRatio.qS (Fv F v) σ S ∈ ({0}ᶜ : Set (Fv F v))} :=
    (FibreRatio.continuous_qS (Fv F v) htr).measurable hVm
  have hmass := FibreRatio.mass_eq_lintegral (Fv F v) hCM hJ hm hLm (V := {0}ᶜ) (by simp) (hcq.measurable hVm) hP
  have hconull : coordW (Fv F v) b lam 1 2 {X : Fin 1 → Fin 2 → Fv F v ⊗[F] E | algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ ({0}ᶜ : Set (Fv F v))}ᶜ = 0 := by
    refine measure_mono_null (fun X hX => ?_) n2
    have h0 : algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) = 0 := by simpa using hX
    intro hu
    exact hu.ne_zero h0
  rw [measure_inter_conull hconull, hL1 lam hlam, ← hSm lam hlam.1] at hmass
  have hEmb : MeasurableEmbedding (hermScal (Fv F v) σ) :=
    (hSh.homeomorph _).isClosedEmbedding.measurableEmbedding
  rw [hEmb.restrict_map, hEmb.lintegral_map] at hmass
  have hpre : hermScal (Fv F v) σ ⁻¹' {S | FibreRatio.qS (Fv F v) σ S ∈ ({0}ᶜ : Set (Fv F v))} = {0}ᶜ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_setOf_eq, FibreRatio.qS_hermScal (Fv F v) hCM s]
  rw [hpre, hres] at hmass
  have hae : AEMeasurable (fun s : Fv F v => m (hermScal (Fv F v) σ s) (latV b v)) lam := by
    have h1 : AEMeasurable (fun s : Fv F v => ENNReal.ofReal (m (hermScal (Fv F v) σ s) (latV b v)).toReal)
        (lam.restrict ({0}ᶜ : Set (Fv F v))) :=
      (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable hVm
    rw [hres] at h1
    refine h1.congr (Eventually.of_forall fun s => ?_)
    exact ENNReal.ofReal_toReal (hfin _).ne
  rw [integral_toReal hae (Eventually.of_forall fun s => hfin _), ← hmass]
  simp

end GlobalTheory.CompanionTheory.SW.StdLat

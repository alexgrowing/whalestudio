import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFibreFreeExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependentStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

open Set

theorem setLIntegral_eq_of_vanish {V : Type} [MeasurableSpace V] (μ : Measure V) {O : Set V}
    (hO : MeasurableSet O) (f : V → ℝ≥0∞) (hf : ∀ v, v ∉ O → f v = 0) :
    ∫⁻ v in O, f v ∂μ = ∫⁻ v, f v ∂μ := by
  rw [← lintegral_indicator hO]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ O
  · rw [indicator_of_mem hv]
  · rw [indicator_of_notMem hv, hf v hv]

theorem lintegral_chart_of_continuous {V Vx Va VY : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace Vx] [MeasurableSpace Va] [MeasurableSpace VY]
    (c : Vx → Va → VY → V) (hc : Measurable fun p : Vx × VY × Va => c p.1 p.2.2 p.2.1)
    (μ : Measure V) (μx : Measure Vx) (μY : Measure VY) (μa : Measure Va)
    [SFinite μx] [SFinite μY] [SFinite μa]
    (O cell : Set V) (Ox : Set Vx) (hO : MeasurableSet O) (hOx : MeasurableSet Ox)
    (hcell : IsOpen cell) (hcO : cell ⊆ O)
    (h1 : ∀ᵐ v ∂μ, v ∈ O → v ∈ cell)
    (h2 : ∀ᵐ y ∂μY, ∀ x ∈ Ox, ∀ a, c x a y ∈ cell)
    (h3 : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ cell → (∀ v, 0 ≤ φ v) →
      Integrable φ μ ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂μ =
        ∫⁻ x, ∫⁻ a, ∫⁻ y, ENNReal.ofReal (φ (c x a y)) ∂μY ∂μa ∂μx)
    (h4 : ∀ x a y, x ∉ Ox → c x a y ∉ O)
    (g : V → ℝ≥0∞) (hg : Measurable g) (hgO : ∀ v, v ∉ O → g v = 0) :
    ∫⁻ v, g v ∂μ = ∫⁻ x, ∫⁻ y, ∫⁻ a, g (c x a y) ∂μa ∂μY ∂μx := by
  let f : Vx × VY × Va → V := fun p => c p.1 p.2.2 p.2.1
  let ρ : Measure (Vx × VY × Va) := (μx.restrict Ox).prod (μY.prod μa)
  have hf : Measurable f := hc
  have key : ∀ G : V → ℝ≥0∞, Measurable G → (∀ v, v ∉ O → G v = 0) →
      ∫⁻ v, G v ∂(ρ.map f) = ∫⁻ x, ∫⁻ y, ∫⁻ a, G (c x a y) ∂μa ∂μY ∂μx := by
    intro G hG hG0
    have e : ∀ x, ∫⁻ q, G (f (x, q)) ∂(μY.prod μa) = ∫⁻ y, ∫⁻ a, G (c x a y) ∂μa ∂μY := fun x =>
      lintegral_prod (fun q => G (f (x, q))) ((hG.comp hf).comp measurable_prodMk_left).aemeasurable
    rw [lintegral_map hG hf]
    show ∫⁻ p, G (f p) ∂((μx.restrict Ox).prod (μY.prod μa)) = _
    rw [lintegral_prod (fun p => G (f p)) (hG.comp hf).aemeasurable]
    simp only [e]
    refine setLIntegral_eq_of_vanish μx hOx _ fun x hx => ?_
    have h0 : ∀ y a, G (c x a y) = 0 := fun y a => hG0 _ (h4 x a y hx)
    simp [h0]
  have hmeq : μ.restrict O = ρ.map f := by
    refine GlobalTheory.CompanionTheory.SW.FibreUniq.measure_eq_of_lintegral_eq _ _ cell hcell ?_ ?_ ?_
    · have h : ∀ᵐ v ∂(μ.restrict O), v ∈ cell := (ae_restrict_iff' hO).2 h1
      exact h
    · rw [Measure.map_apply hf hcell.measurableSet.compl]
      have a1 : ∀ᵐ p ∂ρ, p.1 ∈ Ox :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hOx)
      have a2 : ∀ᵐ q ∂(μY.prod μa), ∀ x ∈ Ox, ∀ a, c x a q.1 ∈ cell :=
        Measure.quasiMeasurePreserving_fst.ae h2
      have a3 : ∀ᵐ p ∂ρ, ∀ x ∈ Ox, ∀ a, c x a p.2.1 ∈ cell :=
        Measure.quasiMeasurePreserving_snd.ae a2
      have h : ∀ᵐ p ∂ρ, f p ∈ cell := by
        filter_upwards [a1, a3] with p h h' using h' _ h _
      exact h
    · intro φ hφ hs hsup h0
      obtain ⟨hi, hl⟩ := h3 φ hφ hs hsup h0
      have hm : Measurable fun v => ENNReal.ofReal (φ v) :=
        ENNReal.measurable_ofReal.comp hφ.measurable
      have hv : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := fun v hv => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hv (hcO (hsup h)), ENNReal.ofReal_zero]
      refine ⟨hi.restrict, ?_⟩
      rw [key _ hm hv, setLIntegral_eq_of_vanish μ hO _ hv, hl]
      refine lintegral_congr fun x => ?_
      have hH : Measurable fun q : VY × Va => ENNReal.ofReal (φ (c x q.2 q.1)) :=
        (hm.comp hf).comp measurable_prodMk_left
      exact (lintegral_lintegral_swap hH.aemeasurable).symm
  rw [← key g hg hgO, ← hmeq, setLIntegral_eq_of_vanish μ hO g hgO]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

open Set

theorem stages_zero_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(m 0) = ∫⁻ x, ∫⁻ Y, ∫⁻ a, g (chartS R σ J x a 0 Y) ∂(coordW R b lam 1 n) ∂(m' 0) ∂(m₁ 0) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n d b lam hlam m m₁ m' hm hm₁ hm' g hg hg0
  obtain ⟨hOpen, hLI, hGr, hCh, hmeas⟩ := GlobalTheory.T.free_cell_open_independent F E σ hCM M J hJ R hR n
  have hOpen0 := (GlobalTheory.T.free_cell_open_independent F E σ hCM M J hJ R hR 0).1
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, -⟩ := hR'
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 (n + 1) (M + 2)
  haveI := t8 1 (M + 2)
  haveI := t8 1 n
  haveI := t8 n M
  haveI : SigmaFinite (m₁ 0) :=
    GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_free σ hCM (hypOne J) R hR 1 _ _ m₁ hm₁ 0
  haveI : SigmaFinite (m' 0) :=
    GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_free σ hCM J R hR n _ _ m' hm' 0
  haveI : (coordW R b lam 1 n).IsAddHaarMeasure :=
    (GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam).2.1 1 n
  have hOx : MeasurableSet {x : Fin 1 → Fin (M + 2) → R ⊗[F] E | IsUnit (x 0 0)} := by
    have e : {x : Fin 1 → Fin (M + 2) → R ⊗[F] E | IsUnit (x 0 0)} =
        freeCell (R ⊗[F] E) M 0 := by
      ext x
      exact ⟨fun h => ⟨h, linearIndependent_empty_type⟩, fun h => h.1⟩
    rw [e]
    exact hOpen0.measurableSet
  have hO : MeasurableSet {X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E | IsUnit (X 0 0)} := by
    have hp : Measurable fun (X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) (_ : Fin 1) => X 0 :=
      measurable_pi_lambda _ fun _ => measurable_pi_apply 0
    exact hp hOx
  have hc : Measurable fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) ×
      (Fin 1 → Fin n → R ⊗[F] E) => chartS R σ J p.1 p.2.2 0 p.2.1 :=
    hmeas.comp (measurable_fst.prodMk ((measurable_snd.comp measurable_snd).prodMk
      (measurable_const.prodMk (measurable_fst.comp measurable_snd))))
  have c0 : ∀ᵐ X ∂(m 0), X ∈ (gramR R σ (hypOne J)) ⁻¹' {((0 : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ {X | LinearIndependent (R ⊗[F] E) X} :=
    hm.1 0
  have c1 : ∀ᵐ Y ∂(m' 0), Y ∈ (gramR R σ J) ⁻¹' {((0 : HermR R σ n) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩ {X | LinearIndependent (R ⊗[F] E) X} :=
    hm'.1 0
  refine lintegral_chart_of_continuous (fun x a Y => chartS R σ J x a 0 Y) hc (m 0) (m₁ 0) (m' 0)
    (coordW R b lam 1 n) {X | IsUnit (X 0 0)} (freeCell (R ⊗[F] E) M n)
    {x | IsUnit (x 0 0)} hO hOx hOpen (fun X hX => hX.1) ?_ ?_ ?_ ?_ g hg hg0
  · filter_upwards [c0] with X hX hu
    exact hGr X hX.2 hX.1 hu
  · filter_upwards [c1] with Y hY x hx a
    exact hCh x a 0 Y hx hY.2
  · intro φ hφ hs hsup h0
    exact ⟨(hm.2.2 φ hφ hs (hsup.trans fun X hX => hLI X hX)).1 0 (mem_univ _),
      GlobalTheory.T.hyperbolic_fibre_free_extension F E σ hCM M J hJ R hR n d b lam hlam m m₁ m' hm hm₁ hm' φ hφ hs hsup h0⟩
  · intro x a Y hx h
    exact hx (by simpa [chartS] using h)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

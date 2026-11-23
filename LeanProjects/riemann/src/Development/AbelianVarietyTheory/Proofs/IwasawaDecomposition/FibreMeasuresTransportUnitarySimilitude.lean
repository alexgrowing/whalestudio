import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnitsStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem isFibreFamily_transport {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure V) (ν : Measure R) (q q₂ : V → R) (e : V ≃ₜ V) (u : Rˣ) (a d : ℝ≥0) (hd : d ≠ 0)
    (hμ : μ = a • μ.map e) (hν : ν = d • ν.map (fun z => (u : R) * z))
    (hq : ∀ v, q₂ (e v) = u * q v) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν {c | IsUnit c} fib) :
    IsFibreFamily μ q₂ id Set.univ ν {c | IsUnit c}
      (fun b => (a * d⁻¹) • (fib ((u⁻¹ : Rˣ) * b)).map e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmu : MeasurableEmbedding (fun z : R => (u : R) * z) :=
    (Homeomorph.smul u : R ≃ₜ R).measurableEmbedding
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc _ => ?_⟩
  · rw [Measure.smul_apply, hme.map_apply]
    have : e ⁻¹' (q₂ ⁻¹' {id b} ∩ Set.univ)ᶜ = (q ⁻¹' {id ((u⁻¹ : Rˣ) * b)} ∩ Set.univ)ᶜ := by
      ext v
      simp [hq, Units.eq_inv_mul_iff_mul_eq]
    rw [this, h1, smul_zero]
  · have h2' := h2 (φ ∘ e) (hφ.comp e.measurable)
    simp only [Measure.restrict_univ, Function.comp] at h2' ⊢
    have hL : ∫⁻ v, φ v ∂μ = (a : ℝ≥0∞) * ∫⁻ v, φ (e v) ∂μ := by
      conv_lhs => rw [hμ]
      rw [lintegral_smul_measure, hme.lintegral_map, ENNReal.smul_def, smul_eq_mul]
    rw [hL, h2']
    conv_rhs => rw [hν]
    rw [lintegral_smul_measure, hmu.lintegral_map]
    simp only [lintegral_smul_measure, hme.lintegral_map, Units.inv_mul_cancel_left,
      ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul]
    congr 2
    field_simp
  · obtain ⟨h4, h5⟩ := h3 (φ ∘ e) (hφ.comp e.continuous) (hc.comp_homeomorph e) (Set.subset_univ _)
    have hmem : ∀ b ∈ {c : R | IsUnit c}, ((u⁻¹ : Rˣ) : R) * b ∈ {c : R | IsUnit c} :=
      fun b hb => (Units.isUnit _).mul hb
    refine ⟨fun b hb => ?_, ?_⟩
    · exact (hme.integrable_map_iff.2 (h4 _ (hmem b hb))).smul_measure_nnreal
    · simp only [integral_smul_nnreal_measure, hme.integral_map]
      exact (h5.comp (continuous_const.mul continuous_id).continuousOn hmem).const_smul _

theorem lrAct_one_right {S : Type} [CommRing S] {n M : ℕ} (g : Matrix (Fin M) (Fin M) S)
    (X : Fin n → Fin M → S) : lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

theorem exists_homeomorph_lrAct {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    {n M : ℕ} (g : Matrix (Fin M) (Fin M) S) (hg : IsUnit g.det) :
    ∃ e : (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S), ⇑e = lrAct g 1 := by
  refine ⟨{ toFun := fun X a => g.mulVec (X a)
            invFun := fun X a => g⁻¹.mulVec (X a)
            left_inv := fun X => ?_
            right_inv := fun X => ?_
            continuous_toFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a)
            continuous_invFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a) }, ?_⟩
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg]
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hg]
  · funext X
    rw [lrAct_one_right]
    rfl

theorem fibAt_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J J₂ : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β c : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit g.det → IsUnit c → (∀ z, qR R σ J₂ (g.mulVec z) = c * qR R σ J z) → FibAt R σ J (tupMeas lam 1 M) ν β m → FibAt R σ J₂ (tupMeas lam 1 M) ν (c * β) ((modu (R ⊗[F] E) g.det * (modu R c)⁻¹) • m.map (lrAct g 1)) := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hR M J J₂ lam ν β c m g hlam hν hg hc hq hfib
  obtain ⟨fib, hfib, rfl⟩ := hfib
  obtain ⟨hA, hred, -⟩ := GlobalTheory.T.tensor_niceRing_artinian_reduced_openUnits F E R hR
  have hμ := GlobalTheory.T.vectorTupleProductMeasure_two_sided_action (R ⊗[F] E) hA hred lam hlam 1 M g 1 hg (by simp)
  rw [Matrix.det_one, (modu_basic (R ⊗[F] E)).2.2.1, one_pow, mul_one, pow_one] at hμ
  obtain ⟨e, he⟩ := exists_homeomorph_lrAct (n := 1) g hg
  obtain ⟨hpos, hν'⟩ := (modu_basic R).1 c hc
  obtain ⟨u, rfl⟩ := hc
  rw [← he] at hμ ⊢
  refine ⟨_, isFibreFamily_transport _ ν _ _ e u _ _ hpos.ne' hμ (hν' ν hν) (fun X => ?_) fib hfib, ?_⟩
  · rw [he, lrAct_one_right]
    exact hq _
  · simp only [Units.inv_mul_cancel_left]

end GlobalTheory.GaugeEx

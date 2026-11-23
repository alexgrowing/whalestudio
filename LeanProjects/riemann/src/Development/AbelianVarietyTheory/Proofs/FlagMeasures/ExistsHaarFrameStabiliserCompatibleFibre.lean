import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegrationFormulaOrbitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureLocalUnitaryInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramFibreMeasureFreeTupleNeZeroFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmulLocalWittFreeTupleGramStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalStabiliserHaar

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, Formalism.UG.hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

theorem linearIndependent_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type)
    [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : HA R σ J) {X : Fin a → Fin n → R ⊗[F] E} (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (g • X) := by
  have hker : LinearMap.ker (lin R σ J g) = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y hxy => ?_
    rw [← lin_inv_lin R σ J g x, hxy, lin_inv_lin]
  exact hX.map' (lin R σ J g) hker

theorem exists_haar_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure ∧ ((fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT)) {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y} = 0 ∧ ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∀ s : (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y) → s y • ratTup (Fv F v) (F0 P) = y) → ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ0 ∂(fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT))) := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP hT μ ν hμ hν fib hfib μG hμG
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := GlobalTheory.T.localUnitaryGroup_tuples_topological_facts F E σ hCM n J hJ v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := h5
  haveI := h6
  haveI := h7
  haveI := h8
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HA (Fv F v) σ J) := ⟨rfl⟩
  obtain ⟨-, -, -, -, hfree⟩ := GlobalTheory.T.standardFrame_gram_det_ne_zero F E σ hCM n J hJ r P T hP
  have hx0 := hfree v
  set x0 := ratTup (F := F) (Fv F v) (F0 P) with hx0def
  set S := hermOf (Fv F v) σ (gramE σ J (F0 P)) hT with hS
  have hgram : gramR (Fv F v) σ J x0 = (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :=
    gramR_ratTup (Fv F v) σ J (F0 P)
  obtain ⟨hne, hfin⟩ := GlobalTheory.T.gramFibreMeasure_freeTuple_ne_zero_finite F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib x0 S hx0 hgram
  have hinv := GlobalTheory.T.gramMap_fibreMeasure_localUnitary_invariant F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib S
  have hcont := (h9 (r + 1)).2
  have hnull : (fib S) {y | ¬ ∃ g : HA (Fv F v) σ J, g • x0 = y} = 0 := by
    refine measure_mono_null (fun y hy => ?_) (hfib.1 S)
    intro hmem
    exact hy (GlobalTheory.T.exists_smul_localWitt_free_tuple_gram F E σ hCM n J hJ v r P T hP y hmem.2 hmem.1)
  have hsmul : ∀ g : HA (Fv F v) σ J, Continuous
      (fun y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E => g • y) := fun g =>
    hcont.comp (Continuous.prodMk continuous_const continuous_id)
  have hinv' : ∀ (g : HA (Fv F v) σ J) (s : Set (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)),
      MeasurableSet s → (fib S) ((fun y => g • y) ⁻¹' s) = (fib S) s := by
    intro g s hs
    rw [← Measure.map_apply (hsmul g).measurable hs, hinv g]
  have hcpt : ∀ K : Set (HA (Fv F v) σ J), IsCompact K →
      (fib S) ((fun g => g • x0) '' K) < ⊤ := by
    intro K hK
    refine hfin _ (hK.image ?_) ?_
    · exact hcont.comp (Continuous.prodMk continuous_id continuous_const)
    · rintro _ ⟨g, -, rfl⟩
      exact linearIndependent_smul (Fv F v) σ J g hx0
  obtain ⟨μ0, hμ0, hw⟩ := GlobalTheory.T.weil_integration_formula_orbit (HA (Fv F v) σ J) (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) x0
    hcont μG hμG (fib S) hnull hinv' hcpt hne
  exact ⟨μ0, hμ0, hnull, hw⟩

end GlobalTheory.LocalStabiliserHaar

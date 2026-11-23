import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SelfDualTransport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarEqProductLocalMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuples
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsFiniteAdeleHaarNormalized
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsEqAdelicCharMul
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement

noncomputable section
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem measurableSet_latV (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  exact ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2.measurableSet

theorem coordW_latV (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v)) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    coordW (Fv F v) b (lam v) n M (latV b v) = 1 := by
  classical
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  have hm := measurableSet_latV σ hCM b n M
  have e0 := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d b lam hlam lf hlf h1 n M ∅ (fun w => latV b w) hm
  have e1 := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d b lam hlam lf hlf h1 n M {v} (fun w => latV b w) hm
  have hs : {X : Fin n → Fin M → Af F ⊗[F] E | (∀ w ∈ ({v} : Finset _), projV w X ∈ latV b w) ∧ ∀ w, w ∉ ({v} : Finset _) → projV w X ∈ latV b w} =
      {X | (∀ w ∈ (∅ : Finset _), projV w X ∈ latV b w) ∧ ∀ w, w ∉ (∅ : Finset _) → projV w X ∈ latV b w} := by
    ext X
    simp only [Set.mem_setOf_eq, Finset.mem_singleton, Finset.notMem_empty, false_imp_iff, implies_true, true_and, not_false_eq_true, forall_true_left]
    constructor
    · rintro ⟨h, h'⟩ w
      by_cases hw : w = v
      · exact h w hw
      · exact h' w hw
    · exact fun h => ⟨fun w _ => h w, fun w _ => h w⟩
  rw [hs, e0] at e1
  simpa using e1.symm

theorem sfinite_coordW (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (n M : ℕ) : SFinite (coordW (Af F) b lf n M) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hKf : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Af F) b) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.1 d b
  haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Af F) hKf lf
  unfold coordW
  infer_instance

theorem lint_fin (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v))
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1)
    (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞) (hφ : ∀ v, Measurable (φ v)) :
    Measurable (({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      fun Y => ∏ v ∈ S, φ v (projV v Y)) ∧
    ∫⁻ Y, ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      (fun Y => ∏ v ∈ S, φ v (projV v Y)) Y ∂(coordW (Af F) b lf n M) =
      ∏ v ∈ S, ∫⁻ X, φ v X ∂(coordW (Fv F v) b (lam v) n M) := by
  classical
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M
  have hBv : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => by
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  have hSFv : ∀ v, SigmaFinite (coordW (Fv F v) b (lam v) n M) := fun v => by
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI := (hlam v).1
    have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Fv F v) b) :=
      (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.1 d b
    haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Fv F v) hK (lam v)
    unfold coordW
    infer_instance
  have hcV : ∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) :=
    (GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.1
  have hpv : ∀ v, Measurable (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) := fun v => by
    haveI := hBv v
    exact (hcV v).measurable
  have hlat := measurableSet_latV σ hCM b n M
  set A : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} with hA
  have hAm : MeasurableSet A := by
    have : A = ⋂ v, ⋂ (_ : v ∉ S), projV v ⁻¹' latV b v := by
      ext Y; simp [hA]
    rw [this]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hpv v (hlat v)
  have hfm : Measurable fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ v ∈ S, φ v (projV v Y) :=
    Finset.measurable_prod _ fun v _ => (hφ v).comp (hpv v)
  refine ⟨hfm.indicator hAm, ?_⟩
  let ρ : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E) := fun Y v => projV v.1 Y
  have hρ : Measurable ρ := measurable_pi_lambda _ fun v => hpv v.1
  haveI : ∀ v : S, SigmaFinite (coordW (Fv F v.1) b (lam v.1) n M) := fun v => hSFv v.1
  have hmap : ((coordW (Af F) b lf n M).restrict A).map ρ =
      Measure.pi fun v : S => coordW (Fv F v.1) b (lam v.1) n M := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hρ (MeasurableSet.univ_pi hs), Measure.restrict_apply (hρ (MeasurableSet.univ_pi hs))]
    let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
      fun v => if h : v ∈ S then s ⟨v, h⟩ else Set.univ
    have hA' : ∀ v, MeasurableSet (A' v) := fun v => by
      by_cases h : v ∈ S
      · simp only [A', dif_pos h]; exact hs _
      · simp only [A', dif_neg h]; exact MeasurableSet.univ
    have key := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d b lam hlam lf hlf h1 n M S A' hA'
    have hset : ρ ⁻¹' Set.univ.pi s ∩ A = {X | (∀ v ∈ S, projV v X ∈ A' v) ∧ ∀ v, v ∉ S → projV v X ∈ latV b v} := by
      ext X
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, hA, Set.mem_setOf_eq]
      refine and_congr_left fun _ => ⟨fun h v hv => ?_, fun h v => ?_⟩
      · simpa only [A', dif_pos hv] using h ⟨v, hv⟩
      · have := h v.1 v.2
        simpa only [A', dif_pos v.2] using this
    rw [hset, key, ← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [A', dif_pos v.2]
  rw [lintegral_indicator hAm]
  have hG : Measurable fun y : (∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E)) => ∏ v : S, φ v.1 (y v) :=
    Finset.measurable_prod _ fun v _ => (hφ v.1).comp (measurable_pi_apply v)
  have e1 : ∫⁻ Y in A, ∏ v ∈ S, φ v (projV v Y) ∂(coordW (Af F) b lf n M) =
      ∫⁻ y, ∏ v : S, φ v.1 (y v) ∂(((coordW (Af F) b lf n M).restrict A).map ρ) := by
    rw [lintegral_map hG hρ]
    refine lintegral_congr fun Y => ?_
    rw [← Finset.prod_coe_sort S]
  rw [e1, hmap, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (f := fun v : S => φ v.1) fun v => (hφ v.1).aemeasurable,
    ← Finset.prod_coe_sort S]

section Meas
open GroundTheory.Global
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

abbrev intInf (F : Type) [Field F] [NumberField F] : AddSubgroup (Ainf F) :=
  ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range

omit [NumberField E] in

theorem coordW_congr {F : Type} [Field F] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    {m₁ m₂ : MeasurableSpace R} (h : m₁ = m₂) (l₁ : @Measure R m₁) (l₂ : @Measure R m₂) (hl : ∀ s, l₁ s = l₂ s)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    @coordW F E _ _ _ R _ _ _ m₁ d b l₁ n M = @coordW F E _ _ _ R _ _ _ m₂ d b l₂ n M := by
  subst h
  obtain rfl : l₁ = l₂ := Measure.ext fun s _ => hl s
  rfl

theorem std_transfer (laminf : @Measure (Ainf F) measAinf) (hinf : IsStdInf laminf)
    [m : MeasurableSpace (Ainf F)] (hm : m = measAinf) :
    ∃ l : Measure (Ainf F), (∀ s, l s = laminf s) ∧ l.IsAddHaarMeasure ∧
      ∃ D : Set (Ainf F), IsAddFundamentalDomain (intInf F) D l ∧ l D = 1 := by
  subst hm
  obtain ⟨h1, D, h2, h3⟩ := hinf
  exact ⟨laminf, fun _ => rfl, h1, D, h2, h3⟩

theorem isFD_fundamentalSetInfinite (ν : Measure (InfiniteAdeleRing F)) :
    IsAddFundamentalDomain (intInf F) (fundamentalSetInfinite F) ν := by
  refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
  · have hmeas := measurableSet_fundamentalSet F
    have hpre : fundamentalSetInfinite F =
        (fun x : InfiniteAdeleRing F => ((x, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) ⁻¹' fundamentalSet F := by
      ext x
      simp [fundamentalSet, Set.mem_prod, Subring.zero_mem]
    rw [hpre]
    exact (measurable_prodMk_right hmeas).nullMeasurableSet
  · obtain ⟨z, hz, hu⟩ := existsUnique_sub_mem_fundamentalSetInfinite F x
    refine ⟨⟨algebraMap (𝓞 F) (InfiniteAdeleRing F) (-z), -z, rfl⟩, ?_, ?_⟩
    · change algebraMap (𝓞 F) (InfiniteAdeleRing F) (-z) + x ∈ fundamentalSetInfinite F
      rwa [map_neg, neg_add_eq_sub]
    · rintro ⟨_, k, rfl⟩ h
      change algebraMap (𝓞 F) (InfiniteAdeleRing F) k + x ∈ fundamentalSetInfinite F at h
      have hk : -k = z := hu (-k) (by
        change x - algebraMap (𝓞 F) (InfiniteAdeleRing F) (-k) ∈ fundamentalSetInfinite F
        rwa [map_neg, sub_neg_eq_add, add_comm])
      refine Subtype.ext ?_
      change algebraMap (𝓞 F) (InfiniteAdeleRing F) k = algebraMap (𝓞 F) (InfiniteAdeleRing F) (-z)
      rw [← hk, neg_neg]

theorem adele_eq (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    l.prod lf = adeleMeasure F := by
  haveI : Countable (𝓞 F) := inferInstance
  haveI : Countable (intInf F) := by
    have : Function.Surjective ((((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom).rangeRestrict) :=
      AddMonoidHom.rangeRestrict_surjective _
    exact this.countable
  have h2 : l (fundamentalSetInfinite F) = 1 := ((isFD_fundamentalSetInfinite l).measure_eq hD).trans hD1
  set c : ℝ≥0 := Measure.addHaarScalarFactor l (infiniteAdeleMeasure F) with hc
  have hl : l = c • infiniteAdeleMeasure F := Measure.isAddLeftInvariant_eq_smul l (infiniteAdeleMeasure F)
  set s : ℝ≥0 := NNReal.sqrt ‖discr F‖₊ with hs
  have h3 : (c : ℝ≥0∞) * (s : ℝ≥0∞) = 1 := by
    rw [hl, Measure.smul_apply, infiniteAdeleMeasure_fundamentalSetInfinite] at h2
    simpa [ENNReal.smul_def] using h2
  have hset : ({x | ∀ v, x v ∈ v.adicCompletionIntegers F} : Set (Af F)) =
      (integralFiniteAdelesPositiveCompacts F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    exact GroundTheory.Global.mem_integralFiniteAdeles.symm
  have hlf2 : lf = Measure.addHaarMeasure (integralFiniteAdelesPositiveCompacts F) := by
    have := Measure.addHaarMeasure_unique lf (integralFiniteAdelesPositiveCompacts F)
    rw [← hset, h1, one_smul] at this
    exact this
  have hf : ∀ t, lf t = (s : ℝ≥0∞) * finiteAdeleMeasure F t := by
    intro t
    have hs0 : (s : ℝ≥0∞) ≠ 0 := by
      simpa [hs] using sqrt_discr_ne_zero F
    rw [finiteAdeleMeasure, Measure.smul_apply, ← hlf2, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (sqrt_discr_ne_zero F), ← mul_assoc,
      ENNReal.mul_inv_cancel hs0 ENNReal.coe_ne_top, one_mul]
  haveI : SigmaFinite l := by rw [hl]; infer_instance
  haveI : SigmaFinite lf := by rw [hlf2]; infer_instance
  symm
  refine Measure.prod_eq fun A B _ _ => ?_
  rw [Measure.prod_prod, hf B]
  have hA : l A = (c : ℝ≥0∞) * infiniteAdeleMeasure F A := by
    conv_lhs => rw [hl]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hA]
  calc (c : ℝ≥0∞) * infiniteAdeleMeasure F A * ((s : ℝ≥0∞) * finiteAdeleMeasure F B)
      = ((c : ℝ≥0∞) * s) * (infiniteAdeleMeasure F A * finiteAdeleMeasure F B) := by ring
    _ = _ := by rw [h3, one_mul]

end Meas

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

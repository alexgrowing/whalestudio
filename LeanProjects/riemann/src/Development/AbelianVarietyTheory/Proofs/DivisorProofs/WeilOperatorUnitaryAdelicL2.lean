import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open IsDedekindDomain

namespace GlobalTheory.ArchimedeanL2

theorem lintegral_eq_of_fibres {Z X Y : Type} [AddGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [AddGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] (e : Z ≃ₜ+ X × Y) (μ : Measure Z) [μ.IsAddHaarMeasure]
    (ν : Measure X) [ν.IsAddHaarMeasure] {G G' : X × Y → ENNReal} (hG : Measurable G) (hG' : Measurable G')
    (h : ∀ y, ∫⁻ x, G (x, y) ∂ν = ∫⁻ x, G' (x, y) ∂ν) : ∫⁻ z, G (e z) ∂μ = ∫⁻ z, G' (e z) ∂μ := by
  have he : Measurable e := e.continuous.measurable
  let ρ : Measure Y := Measure.addHaar
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  haveI : (ν.prod ρ).IsAddHaarMeasure := inferInstance
  rw [← lintegral_map hG he, ← lintegral_map hG' he, Measure.isAddLeftInvariant_eq_smul (μ.map e) (ν.prod ρ),
    lintegral_smul_measure, lintegral_smul_measure, lintegral_prod_symm _ hG.aemeasurable,
    lintegral_prod_symm _ hG'.aemeasurable]
  simp only [h]

theorem lintegral_sq_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] (g : SchwartzMap V ℂ) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (g x) * g x ∂ν).re := by
  have hi : Integrable (fun x => ‖g x‖ ^ 2) ν := (g.memLp 2 ν).integrable_norm_pow (by norm_num)
  have h1 : ∀ x, star (g x) * g x = ((‖g x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h1]
  rw [integral_complex_ofReal, Complex.ofReal_re,
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable {F : Type} [Field F] [NumberField F]

private theorem cont_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem cont_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

variable (F) in

def splitEquiv (κ : Type) : (κ → AF F) ≃ₜ+ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl
  right_inv p := Prod.ext (funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _) rfl
  map_add' x y := Prod.ext (funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (y i).1) rfl
  continuous_toFun := (continuous_pi fun i => cont_toMixed.comp (continuous_fst.comp (continuous_apply i))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i =>
    (cont_ofMixed.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

theorem lintegral_arch_eq : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : SInf F κ →ₗ[ℂ] SInf F κ) (Ω : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ (f : SInf F κ) (h : (κ → Af F) → ℂ), Ω (pureA F f h) = pureA F (L f) h) →
    (∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
      ∫ x, star (L f₁ x) * L f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖Ω φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ L Ω hΩ hL μ hμ φ hφ
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ → Af F) := borel _
  haveI : BorelSpace (κ → Af F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hφ
  choose f h hh hg using fun i => (g i).2
  let ν : Measure (κ → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hB : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  have hν : ν.IsAddHaarMeasure := inferInstance
  have hsq : ∀ u : SInf F κ, ∫⁻ x, ‖u x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (u x) * u x ∂ν).re := fun u =>
    @lintegral_sq_eq (κ → mixedEmbedding.mixedSpace F) _ _ _ _ hB ν hν u
  haveI : OpensMeasurableSpace ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
    (Prod.borelSpace (α := κ → mixedEmbedding.mixedSpace F) (β := κ → Af F)).opensMeasurable
  have hm : ∀ u : Fin n → SInf F κ, Measurable fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) =>
      ‖∑ i, c i * (u i p.1 * h i p.2)‖ₑ ^ 2 := fun u =>
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      (((u i).continuous.comp continuous_fst).mul ((hh i).1.continuous.comp continuous_snd))).measurable.enorm.pow_const 2
  have hs : ∀ (u : Fin n → SInf F κ) (y : κ → Af F) (x : κ → mixedEmbedding.mixedSpace F),
      ∑ i, c i * (u i x * h i y) = (∑ i, (c i * h i y) • u i) x := fun u y x => by
    rw [sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_apply, smul_eq_mul]; ring
  have key := lintegral_eq_of_fibres (splitEquiv F κ) μ ν (hm fun i => L (f i)) (hm f) fun y => by
    simp only [hs]
    have e : ∑ i, (c i * h i y) • L (f i) = L (∑ i, (c i * h i y) • f i) := by simp only [map_sum, map_smul]
    rw [e, hsq, hsq, hL ν hν]
  have e1 : Ω (∑ i, c i • (g i : (κ → AF F) → ℂ)) = ∑ i, c i • pureA F (L (f i)) (h i) := by
    simp only [map_sum, map_smul, hg, hΩ]
  rw [e1]
  simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact key

end GlobalTheory.ArchimedeanL2

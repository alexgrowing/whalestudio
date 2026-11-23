import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSlice
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass.ClassMeas

theorem slice_le {G V : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [T2Space V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (ν₀ : Measure V) [ν₀.IsAddHaarMeasure]
    (ι : V →+ G) (π : G →+ V) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) {K : Set G}
    (hK : IsCompact K) (h0 : {w | w - ι (π w) ∈ K} ∈ 𝓝 (0 : G)) :
    ∃ c : NNReal, ∀ (J : Type) [Fintype J] (t : J → G) (K' : Set G), IsCompact K' → (∀ k ∈ K, ∃ j, k - t j ∈ K') →
      ∀ f : G → ENNReal, (∀ x, ∀ k ∈ K', f (x + k) = f x) → ∀ x, Measurable (fun y => f (x + ι y)) →
        ∫⁻ y, f (x + ι y) ∂ν₀ ≤ c * (Fintype.card J * ∫⁻ w, f w ∂μ) := by
  set W : Set G := {w | w - ι (π w) ∈ K} with hW
  have hp : Continuous fun w => w - ι (π w) := continuous_id.sub (hι.comp hπ)
  have hV : MeasurableSet W := (hK.isClosed.preimage hp).measurableSet
  have hsub : ∀ B : Set V, π ⁻¹' B ∩ W ⊆ (fun p : G × V => p.1 + ι p.2) '' (K ×ˢ B) := fun B w hw =>
    ⟨(_, _), ⟨hw.2, hw.1⟩, sub_add_cancel _ _⟩
  let ν : Measure V := (μ.restrict W).map π
  have hν : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ W) := fun A hA => by
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have : IsFiniteMeasureOnCompacts ν := ⟨fun A hA => by
    rw [hν A hA.measurableSet]
    exact (measure_mono (hsub A)).trans_lt
      ((hK.prod hA).image (continuous_fst.add (hι.comp continuous_snd))).measure_lt_top⟩
  have : ν.IsAddLeftInvariant := (forall_measure_preimage_add_iff ν).1 fun t A hA => by
    rw [hν A hA, hν _ (measurable_const_add t hA), ← measure_preimage_add μ (ι t) (π ⁻¹' A ∩ W)]
    congr 1
    ext w
    simp only [hW, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, map_add, hπι, add_sub_add_left_eq_sub]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • ν₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul ν ν₀⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := hν Set.univ MeasurableSet.univ
    rw [hc, zero_smul, Set.preimage_univ, Set.univ_inter] at h1
    exact (Measure.measure_pos_of_mem_nhds μ h0).ne h1
  refine ⟨c⁻¹, fun J _ t K' hK' hcov f hf x hm => ?_⟩
  have e1 : ∫⁻ y, f (x + ι y) ∂ν = c * ∫⁻ y, f (x + ι y) ∂ν₀ := by
    rw [hc, lintegral_smul_measure]; rfl
  have e2 : ∫⁻ y, f (x + ι y) ∂ν ≤ Fintype.card J * ∫⁻ w, f w ∂μ := by
    let S : J → Set G := fun j => {w | w - ι (π w) - t j ∈ K'}
    have hS : ∀ j, MeasurableSet (S j) := fun j =>
      (hK'.isClosed.preimage (hp.sub continuous_const)).measurableSet
    have hWS : W ⊆ ⋃ j, S j := fun w hw => Set.mem_iUnion.2 (hcov _ hw)
    rw [lintegral_map hm hπ.measurable]
    refine (lintegral_mono_set hWS).trans ((lintegral_iUnion_le _ _).trans ?_)
    rw [tsum_fintype, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
    rw [setLIntegral_congr_fun (g := fun w => f (x - t j + w)) (hS j) (fun w hw => by
      show f (x + ι (π w)) = f (x - t j + w)
      rw [← hf _ _ hw]
      congr 1
      abel)]
    exact (setLIntegral_le_lintegral _ _).trans (lintegral_add_left_eq_self f _).le
  rw [e1] at e2
  rw [ENNReal.coe_inv hc0]
  exact (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hc0) ENNReal.coe_ne_top).1 e2

variable (F : Type) [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  have : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem isOpen_int : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

theorem card_quot (m : ℕ) : Nat.card (𝓞 F ⧸ Ideal.span {(m : 𝓞 F)}) = m ^ Module.finrank ℤ (𝓞 F) := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
    ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap]
  simp

theorem exists_rep (m : ℕ) (hm : 1 ≤ m) (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    ∃ (q : 𝓞 F ⧸ Ideal.span {(m : 𝓞 F)}) (b : FiniteAdeleRing (𝓞 F) F), (∀ v, b v ∈ v.adicCompletionIntegers F) ∧
      a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) q.out = m * b := by
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F (m : 𝓞 F) (by exact_mod_cast (by omega : m ≠ 0)) a ha
  obtain ⟨s, hs⟩ : ∃ s, s * (m : 𝓞 F) = r - (Ideal.Quotient.mk (Ideal.span {(m : 𝓞 F)}) r).out := by
    rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq]
    exact (Quotient.out_eq _).symm
  refine ⟨Ideal.Quotient.mk _ r, y + algebraMap (𝓞 F) _ s, fun v => add_mem (hy v) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v s), ?_⟩
  have := congrArg (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)) hs
  rw [map_mul, map_sub, map_natCast] at this
  rw [map_natCast] at e
  rw [e]
  linear_combination -this

theorem class_meas : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (a : ℕ) (C : ℝ), ∀ m : ℕ, 1 ≤ m → ∀ f : (κ → AF F) → ENNReal, (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → f (x + (m : AF F) • a') = f x) → ∀ x : κ → AF F, Measurable (fun y : κ → mixedEmbedding.mixedSpace F => f (x + GlobalTheory.SobClass.archInc F y)) → ∫⁻ y : κ → mixedEmbedding.mixedSpace F, f (x + GlobalTheory.SobClass.archInc F y) ≤ ENNReal.ofReal (C * (m : ℝ) ^ a) * ∫⁻ z, f z ∂μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := t2Space_adeleRing_of_numberField F
  refine ⟨Measure.addHaar, inferInstance, ?_⟩
  let ι : (κ → mixedEmbedding.mixedSpace F) →+ (κ → AF F) := AddMonoidHom.mk' (archInc F) archInc_add
  let π : (κ → AF F) →+ (κ → mixedEmbedding.mixedSpace F) := AddMonoidHom.mk' (fun z i => evI F (z i))
    (fun z z' => funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (z i).1 (z' i).1)
  have hι : Continuous ι := continuous_pi fun i =>
    Continuous.prodMk ((continuous_ofMixed F).comp (continuous_apply i)) continuous_const
  have hπ : Continuous π := continuous_pi fun i =>
    (continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))
  have hπι : ∀ y, π (ι y) = y := fun y => funext fun i => evI_archInc y i
  let I : Set (FiniteAdeleRing (𝓞 F) F) := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  let K : Set (κ → AF F) := Set.pi Set.univ fun _ => (({0} : Set (Ainf F)) ×ˢ I : Set (Ainf F × Af F))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_singleton.prod (GlobalTheory.AdeleCocompact.isCompact_integral F)
  have h0 : {w | w - ι (π w) ∈ K} ∈ 𝓝 (0 : κ → AF F) := by
    have ho : IsOpen (Set.pi Set.univ fun _ : κ => {a : AF F | a.2 ∈ I}) :=
      isOpen_set_pi Set.finite_univ fun _ _ => (isOpen_int F).preimage continuous_snd
    refine mem_of_superset (ho.mem_nhds fun i _ v => zero_mem _) fun w hw i _ => ⟨?_, ?_⟩
    · show (w i).1 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1) = 0
      rw [RingEquiv.symm_apply_apply, sub_self]
    · show (w i).2 - 0 ∈ I
      rw [sub_zero]
      exact hw i trivial
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc⟩ := slice_le (Measure.addHaar : Measure (κ → AF F)) volume ι π hι hπ hπι hK h0
  refine ⟨Module.finrank ℤ (𝓞 F) * Fintype.card κ, c, fun m hm f hf x hx => ?_⟩
  have hcard := card_quot F m
  haveI : Finite (𝓞 F ⧸ Ideal.span {(m : 𝓞 F)}) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {(m : 𝓞 F)})
  have key := hc (κ → 𝓞 F ⧸ Ideal.span {(m : 𝓞 F)})
    (fun q i => pairA F 0 (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) (q i).out)) ((fun a => (m : AF F) • a) '' K)
    (hK.image (continuous_const_smul _)) ?_ f ?_ x hx
  · rw [Fintype.card_fun, ← Nat.card_eq_fintype_card, hcard, ← pow_mul, ← mul_assoc] at key
    refine key.trans (le_of_eq ?_)
    congr 1
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  · intro k hk
    choose q b hb e using fun i => exists_rep F m hm (k i).2 (hk i trivial).2
    refine ⟨q, fun i => pairA F 0 (b i), fun i _ => ⟨rfl, hb i⟩, funext fun i => Prod.ext ?_ (e i).symm⟩
    have : (k i).1 = 0 := (hk i trivial).1
    show ((m : AF F)).1 * 0 = (k i).1 - 0
    rw [this, mul_zero, sub_zero]
  · rintro z _ ⟨a, ha, rfl⟩
    refine hf z a fun i => ⟨?_, (ha i trivial).2⟩
    have : (a i).1 = 0 := (ha i trivial).1
    rw [evI, this, map_zero]

end GlobalTheory.SobClass.ClassMeas
end

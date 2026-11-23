import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.WeilM GlobalTheory.AdelicU
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical Topology ContDiff

noncomputable section

namespace GlobalTheory.Cofactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

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

theorem continuous_pureA {f : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (pureA F f g) :=
  (hf.comp (continuous_pi fun i => cont_toMixed.comp (continuous_fst.comp (continuous_apply i)))).mul
    (hg.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))

theorem hasCompactSupport_pureA {f : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) : HasCompactSupport (pureA F f g) := by
  let H : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have hH : Continuous H := continuous_pi fun i =>
    (cont_ofMixed.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)
  refine HasCompactSupport.intro ((hf.isCompact.prod hg.isCompact).image hH) fun x hx => ?_
  by_contra h
  apply hx
  refine ⟨(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2),
    ⟨subset_tsupport _ (left_ne_zero_of_mul h), subset_tsupport _ (right_ne_zero_of_mul h)⟩, ?_⟩
  funext i
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl

variable (F κ) in

theorem exists_bump : ∃ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, HasCompactSupport f ∧ f 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
  have h2 : ContDiff ℝ ∞ fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, h1, ?_⟩
  show (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]

variable (κ) in

def intPts (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F}

theorem intPts_eq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) :
    intPts κ v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
  ext x; simp [intPts]

theorem isCompact_intPts (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : IsCompact (intPts κ v) := by
  rw [intPts_eq]
  exact isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v

theorem isOpen_intPts (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : IsOpen (intPts κ v) := by
  rw [intPts_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {U : Set X} (hc : IsCompact U) (ho : IsOpen U) :
    U.indicator (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]; rfl
  · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem exists_cofactor : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    ∃ (r : (κ → AF F) → ℂ) (K : Set (κ → Fv F v)), @Measurable _ _ (borel _) _ r ∧
      (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r ∈ GlobalTheory.WeilM.schA F κ) ∧
      IsCompact K ∧ (interior K).Nonempty ∧
      ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 ∧
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ := by
  intro F _ _ κ _ v
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨f, hfc, hf0⟩ := exists_bump F κ
  let φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ := fun w => (intPts κ w).indicator 1
  have hφ : ∀ w, φ w ∈ GlobalTheory.WeilM.SB _ := fun w => indicator_mem_SB (isCompact_intPts w) (isOpen_intPts w)
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have key : ∀ ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) ψ r = pureA F f g := by
    intro ψ hψ
    have h1 : ∀ w, Function.update φ v ψ w ∈ GlobalTheory.WeilM.SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hψ
      · rw [Function.update_of_ne hw]; exact hφ w
    have h2 := GlobalTheory.PureFactor.update_eventually φ v ψ hstd
    exact ⟨_, ⟨isLocallyConstant_finprod_evalV _ h1 h2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ h1 h2⟩,
      hrt ψ⟩
  have hev : Continuous fun x : κ → AF F => fun i => evFin F v (x i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (continuous_apply i))
  have h0 : (0 : κ → Fv F v) ∈ intPts κ v := fun _ => zero_mem _
  have hrc : Continuous r := by
    rw [continuous_iff_continuousAt]
    intro x
    let y : κ → Fv F v := fun i => evFin F v (x i)
    let U : Set (κ → Fv F v) := Homeomorph.addRight y '' intPts κ v
    have hUo : IsOpen U := (Homeomorph.addRight y).isOpenMap _ (isOpen_intPts v)
    have hUc : IsCompact U := (isCompact_intPts v).image (Homeomorph.addRight y).continuous
    have hy : y ∈ U := ⟨0, h0, by simp⟩
    obtain ⟨g, hg, e⟩ := key _ (indicator_mem_SB hUc hUo)
    refine (continuous_pureA f.continuous hg.1.continuous).continuousAt.congr ?_
    filter_upwards [hev.continuousAt.preimage_mem_nhds (hUo.mem_nhds hy)] with z hz
    rw [← e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens
    rw [Set.indicator_of_mem (show (fun i => evFin F v (z i)) ∈ U from hz), Pi.one_apply, one_mul]
  refine ⟨r, intPts κ v, hrc.measurable, hr, fun ψ hψ => ?_, isCompact_intPts v,
    ⟨0, by rw [(isOpen_intPts v).interior_eq]; exact h0⟩, fun μ hμ => ?_⟩
  · obtain ⟨g, hg, e⟩ := key ψ hψ
    exact Submodule.subset_span ⟨f, g, hg, e⟩
  obtain ⟨g, hg, e⟩ := key _ (hφ v)
  set P := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r with hP
  have hPc : Continuous P := e ▸ continuous_pureA f.continuous hg.1.continuous
  have hPs : HasCompactSupport P := e ▸ hasCompactSupport_pureA hfc hg.2
  have hP0 : P 0 = 1 := by
    rw [hP, hrt (φ v), Function.update_eq_self]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have a1 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
      funext i
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    rw [a1, hf0, one_mul]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have : (fun i => evFin F w ((0 : κ → AF F) i)) ∈ intPts κ w := by
      intro i
      show evFin F w 0 ∈ _
      rw [map_zero]; exact zero_mem _
    exact Set.indicator_of_mem this _
  have hI : (fun x : κ → AF F => (intPts κ v).indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2) =
      fun x => ‖(P * P) x‖ₑ := by
    funext x
    simp only [hP, Pi.mul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, φ]
    by_cases hx : (fun i => evFin F v (x i)) ∈ intPts κ v
    · simp [Set.indicator_of_mem hx, sq]
    · simp [Set.indicator_of_notMem hx]
  rw [hI]
  have hPP : Continuous (P * P) := hPc.mul hPc
  refine ⟨fun h => ?_, (hPP.integrable_of_hasCompactSupport hPs.mul_left).2.ne⟩
  rw [lintegral_eq_zero_iff hPP.measurable.enorm] at h
  have h3 : (P * P) =ᵐ[μ] 0 := h.mono fun x hx => by simpa using hx
  have h4 := congrFun ((hPP.ae_eq_iff_eq μ continuous_zero).1 h3) 0
  simp [hP0] at h4

end GlobalTheory.Cofactor

end

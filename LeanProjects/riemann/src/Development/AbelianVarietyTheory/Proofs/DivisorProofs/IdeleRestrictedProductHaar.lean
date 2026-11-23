import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitAtUnitArch
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)
noncomputable section

namespace GlobalTheory.ThK.ConeEuler

theorem prod_le_exp_tsum_abs_sub_one {ι : Type} (a : ι → ℝ) (ha : ∀ x, 0 ≤ a x) (hs : Summable fun x => a x - 1)
    (S : Finset ι) : ∏ x ∈ S, a x ≤ Real.exp (∑' x, |a x - 1|) := by
  calc ∏ x ∈ S, a x ≤ ∏ x ∈ S, Real.exp |a x - 1| :=
        Finset.prod_le_prod (fun x _ => ha x) fun x _ => by
          have h1 := le_abs_self (a x - 1)
          have h2 := Real.add_one_le_exp |a x - 1|
          linarith
    _ = Real.exp (∑ x ∈ S, |a x - 1|) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' x, |a x - 1|) :=
        Real.exp_le_exp.2 (hs.abs.sum_le_tsum S fun _ _ => abs_nonneg _)

theorem integral_euler_ideles : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μI : Measure (idelesAt E (evI F))), μI.IsHaarMeasure →
    ∀ (μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), (∀ v, IsNormE E v (μv v)) →
    ∀ (ν : Measure (AE F E)ˣ), GlobalTheory.RestrMeas.IsCylProd (W := Unit) (V := Pl F)
        (fun _ l => (⟨unitArch F E l, unitArch_mem l⟩ : idelesAt E (evI F)))
        (fun v l => (⟨unitAt E v l, unitAt_mem v l⟩ : idelesAt E (evFin F v)))
        (fun v => {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v}) (fun _ => μI) μv ν →
    ∀ (T : Finset (Pl F)) (h : (AE F E)ˣ → ℂ) (q g : Pl F → (AE F E)ˣ → ℂ),
      Integrable (fun l : idelesAt E (evI F) => h l.1) μI →
      (∀ v ∈ T, Integrable (fun l : idelesAt E (evFin F v) => q v l.1) (μv v)) →
      (∀ᶠ v in cofinite, ∀ l ∈ unitsAt E v, g v l = 1) →
      (∀ v ∉ T, Integrable (fun l : idelesAt E (evFin F v) => g v l.1) (μv v)) →
      Summable (fun v : {v : Pl F // v ∉ T} => ∫ l : idelesAt E (evFin F v.1), ‖g v.1 l.1‖ ∂(μv v.1) - 1) →
      Integrable (fun l => h (unitArch F E l) * (∏ v ∈ T, q v (unitAt E v l)) *
          ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l)) ν ∧
      ∫ l, h (unitArch F E l) * (∏ v ∈ T, q v (unitAt E v l)) * ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l) ∂ν =
        (∫ l : idelesAt E (evI F), h l.1 ∂μI) * (∏ v ∈ T, ∫ l : idelesAt E (evFin F v), q v l.1 ∂(μv v)) *
          ∏' v : {v : Pl F // v ∉ T}, ∫ l : idelesAt E (evFin F v.1), g v.1 l.1 ∂(μv v.1) := by
  intro F E _ _ _ _ _ μI hμI μv hμv ν hν T h q g hh hq hg hgi hs
  classical
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  have hfacts := fun v : Pl F => idelesAt_facts E (evFin F v)
  haveI : ∀ v : Pl F, SigmaFinite (μv v) := fun v => by
    obtain ⟨_, _, _, _, _⟩ := hfacts v
    haveI := (hμv v).1
    infer_instance
  haveI : ∀ w : Unit, SigmaFinite ((fun _ : Unit => μI) w) := fun _ => inferInstance
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have ha : ∀ w : Unit, Measurable (fun l : (AE F E)ˣ =>
      (⟨unitArch F E l, unitArch_mem l⟩ : idelesAt E (evI F))) := fun _ =>
    ((continuous_unitAt_unitArch F E).2.subtype_mk _).measurable
  have hf : ∀ v : Pl F, Measurable (fun l : (AE F E)ˣ =>
      (⟨unitAt E v l, unitAt_mem v l⟩ : idelesAt E (evFin F v))) := fun v => by
    obtain ⟨_, _, _, _, _⟩ := hfacts v
    exact (((continuous_unitAt_unitArch F E).1 v).subtype_mk _).measurable
  have hK : ∀ v : Pl F, MeasurableSet {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} := fun v => by
    obtain ⟨_, _, _, _, _⟩ := hfacts v
    exact (isCompact_isOpen_unitsAt v).2.measurableSet
  have hX : ∀ l : (AE F E)ˣ, ∀ᶠ v in cofinite,
      (⟨unitAt E v l, unitAt_mem v l⟩ : idelesAt E (evFin F v)) ∈ {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} :=
    fun l => eventually_unitAt_mem_unitsAt F E l
  obtain ⟨Z, hZ⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually hg
  let ff : ∀ v : Pl F, idelesAt E (evFin F v) → ℂ := fun v y => if v ∈ T then q v y.1 else g v y.1
  let fa : ∀ _ : Unit, idelesAt E (evI F) → ℂ := fun _ y => h y.1
  have hS : ∀ v ∉ T ∪ Z, μv v {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} = 1 := fun v _ => (hμv v).2
  have h1 : ∀ v ∉ T ∪ Z, ∀ y ∈ {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v}, ff v y = 1 := fun v hv y hy => by
    have hT : v ∉ T := fun h' => hv (Finset.mem_union_left _ h')
    simp only [ff, if_neg hT]
    exact hZ v (fun h' => hv (Finset.mem_union_right _ h')) _ hy
  have hfa : ∀ w, Integrable (fa w) μI := fun _ => hh
  have hff : ∀ v, Integrable (ff v) (μv v) := fun v => by
    by_cases hv : v ∈ T
    · simp only [ff, if_pos hv]; exact hq v hv
    · simp only [ff, if_neg hv]; exact hgi v hv

  set A : {v : Pl F // v ∉ T} → ℝ := fun v => ∫ l : idelesAt E (evFin F v.1), ‖g v.1 l.1‖ ∂(μv v.1) with hA
  have hA0 : ∀ v, 0 ≤ A v := fun v => integral_nonneg fun _ => norm_nonneg _
  set C : ℝ := (∏ v ∈ T, ∫ l : idelesAt E (evFin F v), ‖q v l.1‖ ∂(μv v)) * Real.exp (∑' v, |A v - 1|) with hC'
  have hC : ∀ S : Finset (Pl F), T ∪ Z ⊆ S → ∏ v ∈ S, ∫ y, ‖ff v y‖ ∂μv v ≤ C := fun S hS' => by
    have hTS : T ⊆ S := Finset.subset_union_left.trans hS'
    rw [← Finset.union_sdiff_of_subset hTS, Finset.prod_union Finset.disjoint_sdiff]
    have e1 : ∏ v ∈ T, ∫ y, ‖ff v y‖ ∂μv v = ∏ v ∈ T, ∫ l : idelesAt E (evFin F v), ‖q v l.1‖ ∂(μv v) :=
      Finset.prod_congr rfl fun v hv => by simp only [ff, if_pos hv]
    have e2 : ∏ v ∈ S \ T, ∫ y, ‖ff v y‖ ∂μv v = ∏ v ∈ (S \ T).subtype (· ∉ T), A v := by
      rw [← Finset.prod_subtype_of_mem (fun v => ∫ y, ‖ff v y‖ ∂μv v) fun v hv => (Finset.mem_sdiff.1 hv).2]
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [ff, if_neg v.2, A]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (prod_le_exp_tsum_abs_sub_one A hA0 hs _)
      (Finset.prod_nonneg fun v _ => integral_nonneg fun _ => norm_nonneg _)
  have hint := hν.integrable_tensor ha hf hK hX hS h1 hfa hff hC
  have heq := hν.integral_tensor_eq_tprod ha hf hK hX hS h1 hfa hff hC

  have hpt : (fun l : (AE F E)ˣ => (∏ w : Unit, fa w (⟨unitArch F E l, unitArch_mem l⟩ : idelesAt E (evI F))) *
      ∏ᶠ v, ff v (⟨unitAt E v l, unitAt_mem v l⟩ : idelesAt E (evFin F v))) =
      fun l => h (unitArch F E l) * (∏ v ∈ T, q v (unitAt E v l)) *
        ∏ᶠ (v : Pl F) (_ : v ∉ T), g v (unitAt E v l) := by
    funext l
    obtain ⟨Y, hY⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually (hX l)
    have hsub : ∀ v ∉ (T ∪ Z) ∪ Y, ∀ y ∈ {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v}, ff v y = 1 :=
      fun v hv => h1 v fun h' => hv (Finset.mem_union_left _ h')
    rw [GlobalTheory.RestrMeas.finprod_eq_prod_of_mem (K := fun v => {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v})
      (pf := fun v (l : (AE F E)ˣ) => (⟨unitAt E v l, unitAt_mem v l⟩ : idelesAt E (evFin F v))) (x := l)
      hsub (fun v hv => hY v fun h' => hv (Finset.mem_union_right _ h'))]
    rw [finprod_cond_eq_prod_of_cond_iff (t := ((T ∪ Z) ∪ Y) \ T) _ ?_]
    · rw [Finset.univ_unique, Finset.prod_singleton, mul_assoc]
      congr 1
      simp only [ff]
      rw [Finset.prod_ite]
      congr 1
      · refine Finset.prod_congr ?_ fun _ _ => rfl
        ext v; simp only [Finset.mem_filter, Finset.mem_union]; tauto
      · refine Finset.prod_congr ?_ fun _ _ => rfl
        ext v; simp only [Finset.mem_filter, Finset.mem_sdiff]
    · intro v hv
      constructor
      · intro hvT
        refine Finset.mem_sdiff.2 ⟨?_, hvT⟩
        by_contra hvS
        apply hv
        have := h1 v (fun h' => hvS (Finset.mem_union_left _ h')) _ (hY v fun h' => hvS (Finset.mem_union_right _ h'))
        simpa only [ff, if_neg hvT] using this
      · exact fun hv' => (Finset.mem_sdiff.1 hv').2
  rw [hpt] at hint heq
  refine ⟨hint, heq.trans ?_⟩
  rw [Finset.univ_unique, Finset.prod_singleton, mul_assoc]
  congr 1

  have hmA := GlobalTheory.RestrMeas.multipliable_integral (V := {v : Pl F // v ∉ T})
    (K := fun v => {l : idelesAt E (evFin F v.1) | l.1 ∈ unitsAt E v.1})
    (ff := fun v y => g v.1 y.1) (S₀ := Z.subtype (· ∉ T)) (fun v => hK v.1) (fun v _ => (hμv v.1).2)
    (fun v hv y hy => hZ v.1 (fun h' => hv (Finset.mem_subtype.2 h')) y hy) (fun v => hgi v.1 v.2)
    (C := Real.exp (∑' v, |A v - 1|)) fun S _ => prod_le_exp_tsum_abs_sub_one A hA0 hs S
  have hP : HasProd (fun v => ∫ y, ff v y ∂μv v)
      ((∏ v ∈ T, ∫ l : idelesAt E (evFin F v), q v l.1 ∂(μv v)) *
        ∏' v : {v : Pl F // v ∉ T}, ∫ l : idelesAt E (evFin F v.1), g v.1 l.1 ∂(μv v.1)) := by
    refine HasProd.mul_isCompl (s := (T : Set (Pl F))) (t := (T : Set (Pl F))ᶜ) isCompl_compl ?_ ?_
    · have := T.hasProd (fun v => ∫ y, ff v y ∂μv v)
      convert this using 1
      exact Finset.prod_congr rfl fun v hv => by simp only [ff, if_pos hv]
    · let e : ((T : Set (Pl F))ᶜ : Set (Pl F)) ≃ {v : Pl F // v ∉ T} :=
        Equiv.subtypeEquivRight fun v => by simp
      have hfe : (fun v => ∫ y, ff v y ∂μv v) ∘ ((↑) : ((T : Set (Pl F))ᶜ : Set (Pl F)) → Pl F) =
          (fun v : {v : Pl F // v ∉ T} => ∫ l : idelesAt E (evFin F v.1), g v.1 l.1 ∂(μv v.1)) ∘ e := by
        funext v
        have hv : (v : Pl F) ∉ T := v.2
        simp only [Function.comp_apply, ff, if_neg hv]
        rfl
      rw [hfe]
      exact e.hasProd_iff.2 hmA.hasProd
  exact hP.tprod_eq

end GlobalTheory.ThK.ConeEuler

end

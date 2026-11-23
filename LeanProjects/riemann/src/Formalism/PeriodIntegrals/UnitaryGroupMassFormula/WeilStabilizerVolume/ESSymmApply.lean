import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProdSt

noncomputable section

namespace PI.VolStabW.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))

def am (i : ι) : ℝ≥0 := (m i (L i)).toNNReal

def tl (S : Finset ι) : ℝ≥0 := ∏' i : {i // i ∉ S}, am m L i.1

def TailH : Prop :=
  ∀ S : Finset ι, ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c

variable {m L}

lemma hasProd_tl (hT : TailH m L) (S : Finset ι) :
    HasProd (fun i : {i // i ∉ S} => am m L i.1) (tl m L S) := by
  obtain ⟨c, hc, h⟩ := hT S
  have h2 : HasProd (fun i : {i // i ∉ S} => am m L i.1) c.toNNReal := by
    have h3 := (ENNReal.tendsto_toNNReal hc).comp h
    refine h3.congr ?_
    intro s
    simp [Function.comp_def, am, ENNReal.toNNReal_prod]
  unfold tl
  rw [h2.tprod_eq]
  exact h2

lemma hasProd_ind (hT : TailH m L) (S : Finset ι) :
    HasProd (({i | i ∉ S} : Set ι).mulIndicator (am m L)) (tl m L S) := by
  have h := hasProd_tl hT S
  exact hasProd_subtype_iff_mulIndicator.mp h

lemma tl_split [DecidableEq ι] (hT : TailH m L) {S T : Finset ι} (h : S ⊆ T) :
    tl m L S = (∏ i ∈ T \ S, am m L i) * tl m L T := by
  classical
  have h1 := hasProd_ind hT S
  have h2 := hasProd_ind hT T
  have h3 : HasProd (((T \ S : Finset ι) : Set ι).mulIndicator (am m L)) (∏ i ∈ T \ S, am m L i) := by
    have h5 : HasProd (((T \ S : Finset ι) : Set ι).mulIndicator (am m L))
        (∏ b ∈ T \ S, ((T \ S : Finset ι) : Set ι).mulIndicator (am m L) b) := hasProd_prod_of_ne_finset_one (fun b hb => Set.mulIndicator_apply_eq_one.mpr (fun hb' => absurd (Finset.mem_coe.mp hb') hb))
    convert h5 using 1
    exact Finset.prod_congr rfl (fun i hi => (Set.mulIndicator_of_mem (Finset.mem_coe.mpr hi) _).symm)
  have h4 := h3.mul h2
  refine h1.unique ?_
  convert h4 using 1
  funext i
  by_cases hiS : i ∈ S
  · have hiT := h hiS
    simp [Set.mulIndicator_apply, hiT, hiS]
  · by_cases hiT : i ∈ T <;> simp [Set.mulIndicator_apply, hiT, hiS]

lemma tl_zero [DecidableEq ι] (hT : TailH m L) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (h0 : am m L i = 0) : tl m L S = 0 := by
  rw [tl_split hT (Finset.subset_insert i S), Finset.prod_eq_zero (i := i) (by simp [hi]) h0, zero_mul]

variable (m L)

def Pn (i : ι) : Measure (W i) := (m i (L i))⁻¹ • (m i).restrict (L i)

lemma Pn_prob {i : ι} (h : m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤) : IsProbabilityMeasure (Pn m L i) := by
  constructor
  rw [Pn, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.1 h.2

open Classical in

def Qm (S : Finset ι) : Measure (∀ i : {i // i ∉ S}, W i) :=
  if h : ∀ i, i ∉ S → m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤ then
    haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) := fun i => Pn_prob m L (h i.1 i.2)
    tl m L S • Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)
  else 0

instance Qm_fin (S : Finset ι) : IsFiniteMeasure (Qm m L S) := by
  unfold Qm; split_ifs with h
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (h i.1 i.2)
    infer_instance
  · infer_instance

def Rm (S : Finset ι) : Measure (∀ i : {i // i ∈ S}, W i) :=
  Measure.pi (fun i : {i // i ∈ S} => (m i.1).restrict (L i.1)ᶜ)

open Classical in

def eS (S : Finset ι) : (∀ i, W i) ≃ᵐ (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i) :=
  MeasurableEquiv.piEquivPiSubtypeProd W (fun i => i ∈ S)

def kap [∀ i, SigmaFinite (m i)] (S : Finset ι) : Measure (∀ i, W i) :=
  ((Rm m L S).prod (Qm m L S)).map (eS S).symm

open Classical in

def mu (S : Finset ι) (i : ι) : Measure (W i) :=
  if i ∈ S then (m i).restrict (L i)ᶜ else (m i).restrict (L i)

open Classical in
lemma eS_symm_apply (S : Finset ι) (p : (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i))
    (i : ι) : (eS S).symm p i = if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩ := by
  simp only [eS, MeasurableEquiv.piEquivPiSubtypeProd]
  rfl

variable [∀ i, SigmaFinite (m i)]

instance kap_sfin (S : Finset ι) : SFinite (kap m L S) := by unfold kap Rm; infer_instance

variable {m L}

lemma kap_eval_null {S : Finset ι} {i : ι} {A : Set (W i)} (hA : MeasurableSet A)
    (h : mu m L S i A = 0) : kap m L S {x | x i ∈ A} = 0 := by
  classical
  have hs : MeasurableSet {x : ∀ j, W j | x i ∈ A} := measurable_pi_apply i hA
  unfold kap
  rw [Measure.map_apply (eS S).symm.measurable hs]
  by_cases hi : i ∈ S
  · have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} = ((fun f => f ⟨i, hi⟩) ⁻¹' A) ×ˢ (Set.univ : Set (∀ j : {j // j ∉ S}, W j)) := by
      ext p
      simp [eS_symm_apply, hi]
    have hR : Rm m L S ((fun f => f ⟨i, hi⟩) ⁻¹' A) = 0 := by
      unfold Rm
      apply Measure.pi_eval_preimage_null
      simpa [mu, hi] using h
    rw [hpre, Measure.prod_prod, hR, zero_mul]
  · have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} = (Set.univ : Set (∀ j : {j // j ∈ S}, W j)) ×ˢ ((fun f => f ⟨i, hi⟩) ⁻¹' A) := by
      ext p
      simp [eS_symm_apply, hi]
    have h' : (m i).restrict (L i) A = 0 := by simpa [mu, hi] using h
    have hQ : Qm m L S ((fun f => f ⟨i, hi⟩) ⁻¹' A) = 0 := by
      unfold Qm
      split_ifs with hh
      · haveI : ∀ j : {j // j ∉ S}, IsProbabilityMeasure (Pn m L j.1) := fun j => Pn_prob m L (hh j.1 j.2)
        have h6 : Measure.infinitePi (fun j : {j // j ∉ S} => Pn m L j.1) ((fun f => f ⟨i, hi⟩) ⁻¹' A) = 0 := by
          rw [← Measure.map_apply (measurable_pi_apply (⟨i, hi⟩ : {j // j ∉ S})) hA, Measure.infinitePi_map_eval]
          simp [Pn, h']
        simp [Measure.smul_apply, h6]
      · simp
    rw [hpre, Measure.prod_prod, hQ, mul_zero]

lemma kap_ae [Countable ι] (hLm : ∀ i, MeasurableSet (L i)) (S : Finset ι) :
    ∀ᵐ x ∂kap m L S, ∀ i, (i ∈ S → x i ∉ L i) ∧ (i ∉ S → x i ∈ L i) := by
  classical
  rw [ae_all_iff]
  intro i
  by_cases hi : i ∈ S
  · have h0 : kap m L S {x | x i ∈ L i} = 0 :=
      kap_eval_null (hLm i) (by simp [mu, hi, Measure.restrict_apply (hLm i)])
    refine measure_mono_null (fun x hx => ?_) h0
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hxi
    exact hx ⟨fun _ => hxi, fun h => absurd hi h⟩
  · have h0 : kap m L S {x | x i ∈ (L i)ᶜ} = 0 :=
      kap_eval_null (hLm i).compl (by simp [mu, hi, Measure.restrict_apply (hLm i).compl])
    refine measure_mono_null (fun x hx => ?_) h0
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢
    by_contra hxi
    exact hx ⟨fun h => absurd h hi, fun _ => hxi⟩

end PI.VolStabW.RPA

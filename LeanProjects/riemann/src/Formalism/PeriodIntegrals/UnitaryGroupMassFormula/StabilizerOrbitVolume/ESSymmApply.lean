import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdSt

noncomputable section

namespace PI.VolStabSW.RPA

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
    have := (ENNReal.tendsto_toNNReal hc).comp h
    unfold HasProd at this ⊢
    convert this using 2 with s
    simp [Function.comp, ENNReal.toNNReal_prod, am]
  unfold tl
  rw [h2.tprod_eq]
  exact h2

lemma hasProd_ind (hT : TailH m L) (S : Finset ι) :
    HasProd (({i | i ∉ S} : Set ι).mulIndicator (am m L)) (tl m L S) := hasProd_subtype_iff_mulIndicator.mp (hasProd_tl hT S)

lemma tl_split [DecidableEq ι] (hT : TailH m L) {S T : Finset ι} (h : S ⊆ T) :
    tl m L S = (∏ i ∈ T \ S, am m L i) * tl m L T := by

  have h1 := hasProd_ind hT S
  have h2 := hasProd_ind hT T
  have h3 : HasProd ((↑(T \ S) : Set ι).mulIndicator (am m L)) (∏ i ∈ T \ S, am m L i) := by
    have : HasProd ((↑(T \ S) : Set ι).mulIndicator (am m L))
        (∏ b ∈ T \ S, (↑(T \ S) : Set ι).mulIndicator (am m L) b) :=
      hasProd_prod_of_ne_finset_one (s := T \ S) (f := (↑(T \ S) : Set ι).mulIndicator (am m L))
      (fun b hb => by rw [Set.mulIndicator_apply, if_neg (by simpa using hb)])
    rwa [Finset.prod_congr rfl (fun b hb => by rw [Set.mulIndicator_apply, if_pos (by simpa using hb)])] at this
  have h4 := h3.mul h2
  have e : ({i | i ∉ S} : Set ι).mulIndicator (am m L) =
      (↑(T \ S) : Set ι).mulIndicator (am m L) * ({i | i ∉ T} : Set ι).mulIndicator (am m L) := by
    funext i
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_setOf_eq, Finset.coe_sdiff, Set.mem_diff,
      Finset.mem_coe]
    by_cases hT' : i ∈ T <;> by_cases hS : i ∈ S <;> simp [hT', hS] <;> exact absurd (h hS) hT'
  rw [e] at h1
  exact h1.unique h4

lemma tl_zero [DecidableEq ι] (hT : TailH m L) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (h0 : am m L i = 0) : tl m L S = 0 := by

  rw [tl_split hT (Finset.subset_insert i S), Finset.prod_eq_zero (i := i) (by simp [hi]) h0, zero_mul]

variable (m L)

def Pn (i : ι) : Measure (W i) := (m i (L i))⁻¹ • (m i).restrict (L i)

lemma Pn_prob {i : ι} (h : m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤) : IsProbabilityMeasure (Pn m L i) := by

  constructor
  simp only [Pn, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
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

  first
    | rfl
    | simp [eS, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]

variable [∀ i, SigmaFinite (m i)]

instance kap_sfin (S : Finset ι) : SFinite (kap m L S) := by unfold kap Rm; infer_instance

variable {m L}

lemma kap_eval_null {S : Finset ι} {i : ι} {A : Set (W i)} (hA : MeasurableSet A)
    (h : mu m L S i A = 0) : kap m L S {x | x i ∈ A} = 0 := by

  classical
  have hs : MeasurableSet {x : ∀ i, W i | x i ∈ A} := measurable_pi_apply i hA
  unfold kap
  rw [Measure.map_apply (eS S).symm.measurable hs]
  by_cases hiS : i ∈ S
  · have e : (eS S).symm ⁻¹' {x | x i ∈ A} =
        (Function.eval (⟨i, hiS⟩ : {i // i ∈ S}) ⁻¹' A) ×ˢ Set.univ := by
      ext p; simp [eS_symm_apply, hiS]
    have h0 : ((m i).restrict (L i)ᶜ) A = 0 := by simpa [mu, hiS] using h
    have h1 : Rm m L S (Function.eval (⟨i, hiS⟩ : {i // i ∈ S}) ⁻¹' A) = 0 := by
      unfold Rm
      exact Measure.pi_eval_preimage_null _ h0
    rw [e, Measure.prod_prod, h1, zero_mul]
  · have e : (eS S).symm ⁻¹' {x | x i ∈ A} =
        Set.univ ×ˢ (Function.eval (⟨i, hiS⟩ : {i // i ∉ S}) ⁻¹' A) := by
      ext p; simp [eS_symm_apply, hiS]
    have h0 : ((m i).restrict (L i)) A = 0 := by simpa [mu, hiS] using h
    have h1 : Qm m L S (Function.eval (⟨i, hiS⟩ : {i // i ∉ S}) ⁻¹' A) = 0 := by
      unfold Qm
      split_ifs with hQ
      · haveI : ∀ j : {i // i ∉ S}, IsProbabilityMeasure (Pn m L j.1) := fun j => Pn_prob m L (hQ j.1 j.2)
        rw [Measure.smul_apply, ← Measure.map_apply (show Measurable (Function.eval (⟨i, hiS⟩ : {i // i ∉ S}) :
          (∀ j : {i // i ∉ S}, W j.1) → W i) from measurable_pi_apply _) hA,
          Measure.infinitePi_map_eval]
        simp [Pn, h0]
      · simp
    rw [e, Measure.prod_prod, h1, mul_zero]

lemma kap_ae [Countable ι] (hLm : ∀ i, MeasurableSet (L i)) (S : Finset ι) :
    ∀ᵐ x ∂kap m L S, ∀ i, (i ∈ S → x i ∉ L i) ∧ (i ∉ S → x i ∈ L i) := by

  rw [ae_all_iff]
  intro i
  by_cases hiS : i ∈ S
  · have h0 : kap m L S {x | x i ∈ L i} = 0 :=
      kap_eval_null (hLm i) (by simp [mu, hiS, Measure.restrict_apply (hLm i)])
    rw [ae_iff]
    simpa [hiS] using h0
  · have h0 : kap m L S {x | x i ∈ (L i)ᶜ} = 0 :=
      kap_eval_null (hLm i).compl (by simp [mu, hiS, Measure.restrict_apply (hLm i).compl])
    rw [ae_iff]
    simpa [hiS] using h0

end PI.VolStabSW.RPA

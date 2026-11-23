import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace MeasureInverseInduction

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem countGL : Countable (GL (Fin k) E) := by
  haveI : Countable E := GroundTheory.Global.countable_numberField E
  haveI : Countable (Matrix (Fin k) (Fin k) E) := inferInstanceAs (Countable (Fin k → Fin k → E))
  exact Units.val_injective.countable

theorem blk_ratGL {j : ℕ} {γ : GL (Fin k) E} (h : GlobalTheory j γ) : GlobalTheory j (ratGL E k γ) := by
  intro i c hic
  change algebraMap E (Ad E) (γ.val i c) = _
  rw [h i c hic, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  exact tsum_congr fun γ => lintegral_map hF (measurable_const_mul _)

theorem inv_step (ν : Measure (GA E k)) (hinvν : Measure.map (fun h => h⁻¹) ν = ν) (g : GA E k)
    (hc : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F (g * h * g⁻¹) ∂ν = ∫⁻ h, F h ∂ν)
    (f : GA E k → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * h) ∂ν := by
  have hG : Measurable fun x : GA E k => f (g⁻¹ * (g * x * g⁻¹)) :=
    hf.comp ((measurable_const_mul _).comp ((measurable_mul_const _).comp (measurable_const_mul _)))
  calc ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * (g * h⁻¹ * g⁻¹)) ∂ν :=
        lintegral_congr fun h => by congr 1; group
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂Measure.map (fun h => h⁻¹) ν := (lintegral_map hG measurable_inv).symm
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂ν := by rw [hinvν]
    _ = ∫⁻ x, f (g⁻¹ * x) ∂ν := hc (fun y => f (g⁻¹ * y)) (hf.comp (measurable_const_mul _))

def invE (Γ : Set (GL (Fin k) E)) (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) : Γ ≃ Γ where
  toFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  invFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  left_inv γ := Subtype.ext (inv_inv γ.1)
  right_inv γ := Subtype.ext (inv_inv γ.1)

theorem inv_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ)
    (hinvν : Measure.map (fun h => h⁻¹) (nuD E k d) = nuD E k d)
    (hconj : ∀ γ ∈ Γ, ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ h, F (ratGL E k γ * h * (ratGL E k γ)⁻¹) ∂nuD E k d = ∫⁻ h, F h ∂nuD E k d)
    (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) :
    Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  calc ∫⁻ h, f h ∂Measure.map (fun h => h⁻¹) (nuG Γ d) = ∫⁻ h, f h⁻¹ ∂nuG Γ d :=
        lintegral_map hf measurable_inv
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h)⁻¹ ∂nuD E k d := lint_nuG Γ d _ (hf.comp measurable_inv)
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ.1⁻¹ * h) ∂nuD E k d := tsum_congr fun γ => by
        rw [inv_step _ hinvν _ (hconj γ.1 γ.2) f hf, map_inv (ratGL E k) γ.1]
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d :=
        (invE Γ hΓ).tsum_eq (fun γ : Γ => ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d)
    _ = ∫⁻ h, f h ∂nuG Γ d := (lint_nuG Γ d f hf).symm

theorem sf_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) [SFinite (nuD E k d)] : SFinite (nuG Γ d) := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [nuG]; infer_instance

theorem ae_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (hae : ∀ᵐ u ∂nuD E k d, UU (k - d) u) :
    ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [ae_iff] at hae ⊢
  rw [nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
  intro γ
  rw [(measurableEmbedding_mulLeft (ratGL E k γ)).map_apply]
  exact measure_mono_null (fun u hu hUU => hu ⟨γ.1, u, γ.2, hUU, rfl⟩) hae

theorem nuD_ne_zero (hsf : ∀ d ≤ k, SFinite (nuD E k d)) : ∀ d ≤ k, nuD E k d ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro _ h
    have h1 := congrArg (fun μ : Measure (GA E k) => μ Set.univ) h
    simp [nuD] at h1
  | succ d ih =>
    intro hd h
    haveI := hsf d (by omega)
    have hm : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => blkU p.1 * p.2 :=
      (((continuous_posU (isNil_blk k _ _)).comp continuous_fst).mul continuous_snd).measurable
    have h3 := (Measure.map_eq_zero_iff hm.aemeasurable).mp h
    have h2 := congrArg (fun μ => μ (vecDomain E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) ×ˢ Set.univ)) h3
    simp only [Measure.prod_prod, vecMeasure_vecDomain, one_mul, Measure.coe_zero, Pi.zero_apply] at h2
    exact ih (by omega) (Measure.measure_univ_eq_zero.mp h2)

variable [IsTotallyComplex E]

theorem main_nuG (hD0 : D0) (hN1 : N1) (Γ : Set (GL (Fin k) E)) (d : ℕ) (hd : d ≤ k)
    (hinv : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hblk : ∀ γ ∈ Γ, GlobalTheory (k - d) γ) :
    SFinite (nuG Γ d) ∧ Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d ∧
      ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  obtain ⟨hsf, hae, hinvν, -, hconj⟩ := hN1 E k d hd
  haveI := hsf
  refine ⟨sf_nuG Γ d, inv_nuG Γ d hinvν (fun γ hγ F hF => ?_) hinv, ae_nuG Γ d hae⟩
  rw [hconj _ (blk_ratGL (hblk γ hγ)) F hF, (hD0 E k).2.2.2.1 γ, inv_one, ENNReal.ofReal_one, one_pow, one_mul]

end MeasureInverseInduction

open MeasureInverseInduction in
set_option synthInstance.maxHeartbeats 400000 in
theorem galois_fixed_adelic_matrices_descend : D0 → N0 → N1 → N3 := by
  intro hD0 hN0 hN1 E _ _ _ k
  have hP : ∀ m < k, SFinite (nuP E k m) ∧ Measure.map (fun h => h⁻¹) (nuP E k m) = nuP E k m ∧
      ∀ᵐ h ∂nuP E k m, ∃ γ u, IsMir m γ ∧ UU (m + 1) u ∧ h = ratGL E k γ * u := by
    intro m hm
    have hN := hN0 E k (m + 1) (by omega) (by omega)
    have h6 : ∀ γ : GL (Fin k) E, IsMir m γ → IsMir m γ⁻¹ ∧ GlobalTheory (m + 1) γ := by
      simpa only [Nat.add_sub_cancel] using hN.2.2.2.2.2.1
    have e : k - (k - (m + 1)) = m + 1 := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | IsMir m γ} (k - (m + 1)) (by omega)
      (fun γ hγ => (h6 γ hγ).1) (fun γ hγ => by rw [e]; exact (h6 γ hγ).2)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hB : ∀ j ≤ k, SFinite (nuB E k j) ∧ Measure.map (fun h => h⁻¹) (nuB E k j) = nuB E k j ∧
      ∀ᵐ h ∂nuB E k j, ∃ γ u, GlobalTheory j γ ∧ UU j u ∧ h = ratGL E k γ * u := by
    intro j hj
    have hinv : ∀ γ : GL (Fin k) E, GlobalTheory j γ → GlobalTheory j γ⁻¹ := by
      intro γ hγ
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
        subst this
        rw [inv_one]
        exact hγ
      · exact (hN0 E k j hpos hj).2.2.2.1 γ hγ
    have e : k - (k - j) = j := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | GlobalTheory j γ} (k - j) (by omega)
      (fun γ hγ => hinv γ hγ) (fun γ hγ => by rw [e]; exact hγ)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hall : ∀ γ : GL (Fin k) E, γ ∈ {γ : GL (Fin k) E | GlobalTheory k γ} := fun γ i c h =>
    absurd h (not_or.mpr ⟨not_le.mpr i.isLt, not_le.mpr c.isLt⟩)
  have hK : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F h ∂nuB E k k = ∑' γ : GL (Fin k) E, F (ratGL E k γ) := by
    intro F hF
    rw [nuB, lint_nuG _ _ F hF, Nat.sub_self]
    simp only [nuD, lintegral_dirac, mul_one]
    exact (Equiv.subtypeUnivEquiv hall).tsum_eq (fun γ => F (ratGL E k γ))
  have h4 : 1 ≤ k → (∀ᵐ h ∂nuP E k 0, UU 0 h) ∧ nuP E k 0 ≠ 0 := by
    intro hk
    obtain ⟨-, -, hae⟩ := hP 0 (by omega)
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
      have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
      rw [hh, this, map_one, one_mul]
      exact ⟨hu.1, hu.2.1, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
    · intro h0
      haveI : Countable (GL (Fin k) E) := countGL
      have h1 : nuP E k 0 Set.univ = 0 := by simp [h0]
      rw [nuP, nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero] at h1
      have h2 := h1 ⟨1, show IsMir 0 (1 : GL (Fin k) E) from fun i c _ => rfl⟩
      rw [(measurableEmbedding_mulLeft _).map_apply, Set.preimage_univ, Measure.measure_univ_eq_zero] at h2
      exact nuD_ne_zero (fun d hd => (hN1 E k d hd).1) _ (by omega) h2
  exact ⟨hP, hB, hK, h4⟩

end PositivityTheory.AdelicQuotientData

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTateEpsTateEpsAndNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldTwoVocabulariesDictionary
import GroundTheory.LocalFields.LocalZetaGauss
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.GaussBridge

open GroundTheory.LocalField (valBall unitFiltrationUnits addCharConductor quasiCharConductor
  IsUnramifiedChar unifUnit unitsModRep unitsModFiltration unitsModCoset gaussSum)

local notation "ordF" => GroundTheory.LocalField.ord

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_isSmoothChar {χ : Fˣ →* ℂˣ} (hχ : IsSmoothChar χ) : Continuous χ := by
  refine continuous_def.2 fun U _ => isOpen_iff_forall_mem_open.2 fun x hx => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (χ.ker : Set Fˣ), fun y hy => ?_,
    hχ.preimage (continuous_const_mul _), by simp⟩
  have h : χ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  show χ y ∈ U
  rw [← h]
  exact hx

theorem valuation_le_iff_mem_valBall (x : F) (c : Fˣ) :
    valuation F x ≤ valuation F (c : F) ↔ x ∈ valBall F (ordF (c : F)) := by
  rw [GroundTheory.LocalField.mem_valBall, ← GroundTheory.LocalField.normalizedValuation_eq_exp_ord c.ne_zero,
    GroundTheory.LocalField.normalizedValuation_le_iff]

theorem ord_inv (y : Fˣ) : ordF ((y⁻¹ : Fˣ) : F) = -ordF (y : F) := by
  have := GroundTheory.LocalField.ord_units_mul y y⁻¹
  rw [mul_inv_cancel, Units.val_one, GroundTheory.LocalField.ord_one] at this
  omega

theorem inv_mul_mem_of_sub_mem {a : ℕ} (ha : 1 ≤ a) {y z : Fˣ} {m : ℤ} (hy : ordF (y : F) = m)
    (h : (z : F) - y ∈ valBall F (m + a)) : y⁻¹ * z ∈ unitFiltrationUnits F a := by
  rw [GroundTheory.LocalField.mem_unitFiltrationUnits_iff_valBall ha]
  have hyi : ((y⁻¹ : Fˣ) : F) ∈ valBall F (-m) := by
    rw [GroundTheory.LocalField.mem_valBall_iff_le_ord (y⁻¹).ne_zero, ord_inv, hy]
  have := GroundTheory.LocalField.mul_mem_valBall hyi h
  rw [show -m + (m + (a : ℤ)) = a by ring] at this
  convert this using 1
  rw [Units.val_mul, mul_sub, Units.inv_mul]

theorem sub_mem_of_inv_mul_mem {a : ℕ} {y z : Fˣ} {m : ℤ} (hy : ordF (y : F) = m)
    (h : y⁻¹ * z ∈ unitFiltrationUnits F a) : (z : F) - y ∈ valBall F (m + a) := by
  have h1 := GroundTheory.LocalField.unitFiltration_sub_one_mem_valBall h
  have h2 : (y : F) ∈ valBall F m := (GroundTheory.LocalField.mem_valBall_iff_le_ord y.ne_zero).2 hy.ge
  have := GroundTheory.LocalField.mul_mem_valBall h2 h1
  convert this using 1
  rw [Units.val_mul, mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]

variable {χ : Fˣ →* ℂˣ} {ψ : AddChar F Circle}

theorem term_eq (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hχ : Continuous χ) (hr : ¬ IsUnramifiedChar χ)
    {y z : Fˣ} (hy : ordF (y : F) = addCharConductor ψ - quasiCharConductor χ)
    (h : (z : F) - y ∈ valBall F (addCharConductor ψ)) :
    ((χ z : ℂˣ) : ℂ)⁻¹ * (ψ (z : F) : ℂ) = ((χ y : ℂˣ) : ℂ)⁻¹ * (ψ (y : F) : ℂ) := by
  have ha := GroundTheory.LocalField.quasiCharConductor_pos hχ hr
  have hw := inv_mul_mem_of_sub_mem ha hy (by rwa [sub_add_cancel])
  have hk : χ (y⁻¹ * z) = 1 := GroundTheory.LocalField.unitFiltrationUnits_quasiCharConductor_le_ker hχ hw
  have hχz : χ y * χ (y⁻¹ * z) = χ z := by rw [← map_mul, mul_inv_cancel_left]
  rw [hk, mul_one] at hχz
  have hψz : ψ (z : F) = ψ (y : F) := by
    rw [show (z : F) = y + ((z : F) - y) by ring, AddChar.map_add_eq_mul,
      GroundTheory.LocalField.isTrivialOn_addCharConductor hψ hψ1 _ h, mul_one]
  rw [← hχz, hψz]

theorem sum_shellReps_eq_gaussSum (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hχ : Continuous χ)
    (hr : ¬ IsUnramifiedChar χ) {R : Finset Fˣ}
    (hR1 : ∀ r ∈ R, ordF (r : F) = addCharConductor ψ - quasiCharConductor χ)
    (hR2 : ∀ y : Fˣ, ordF (y : F) = addCharConductor ψ - quasiCharConductor χ →
      ∃! r : Fˣ, r ∈ R ∧ (y : F) - r ∈ valBall F (addCharConductor ψ)) :
    ∑ r ∈ R, ((χ r : ℂˣ) : ℂ)⁻¹ * (ψ (r : F) : ℂ) = gaussSum χ ψ := by
  set m : ℤ := addCharConductor ψ - quasiCharConductor χ with hm
  set π := unifUnit F
  have hy : ∀ t : unitsModFiltration F (quasiCharConductor χ),
      ordF ((π ^ m * unitsModRep t : Fˣ) : F) = m := by
    intro t
    rw [GroundTheory.LocalField.ord_units_mul, GroundTheory.LocalField.ord_unifUnit_zpow,
      GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff_ord.1 (GroundTheory.LocalField.unitsModRep_mem t),
      add_zero]
  let g : unitsModFiltration F (quasiCharConductor χ) → Fˣ := fun t =>
    Classical.choose (hR2 _ (hy t)).exists
  have hg : ∀ t, g t ∈ R ∧ ((π ^ m * unitsModRep t : Fˣ) : F) - g t ∈ valBall F (addCharConductor ψ) :=
    fun t => Classical.choose_spec (hR2 _ (hy t)).exists
  have hnm : m + (quasiCharConductor χ : ℤ) = addCharConductor ψ := by rw [hm, sub_add_cancel]
  have ha := GroundTheory.LocalField.quasiCharConductor_pos hχ hr
  symm
  unfold GroundTheory.LocalField.gaussSum
  refine Finset.sum_bij (fun t _ => g t) (fun t _ => (hg t).1) ?_ ?_ ?_
  · intro t₁ _ t₂ _ h12
    have h1 := (hg t₁).2
    have h2 := (hg t₂).2
    rw [h12] at h1
    have hd : ((π ^ m * unitsModRep t₂ : Fˣ) : F) - ((π ^ m * unitsModRep t₁ : Fˣ) : F) ∈
        valBall F (m + (quasiCharConductor χ : ℤ)) := by
      rw [hnm]
      have := sub_mem h2 h1
      rwa [sub_sub_sub_cancel_right] at this
    have hw := inv_mul_mem_of_sub_mem ha (hy t₁) hd
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left] at hw
    refine GroundTheory.LocalField.eq_of_mem_unitsModCoset (x := unitsModRep t₂)
      (GroundTheory.LocalField.mem_unitsModCoset.2 hw) ?_
    rw [GroundTheory.LocalField.mem_unitsModCoset, inv_mul_cancel]
    exact one_mem _
  · intro r hr
    have hu : π ^ (-m) * r ∈ unitFiltrationUnits F 0 := by
      rw [GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff_ord, GroundTheory.LocalField.ord_units_mul,
        GroundTheory.LocalField.ord_unifUnit_zpow, hR1 r hr]
      ring
    set t : unitsModFiltration F (quasiCharConductor χ) := QuotientGroup.mk ⟨_, hu⟩
    refine ⟨t, Finset.mem_univ _, ?_⟩
    have hc : (unitsModRep t)⁻¹ * (π ^ (-m) * r) ∈ unitFiltrationUnits F (quasiCharConductor χ) :=
      GroundTheory.LocalField.mem_unitsModCoset.1 (GroundTheory.LocalField.mem_unitsModCoset_mk (c := quasiCharConductor χ) hu)
    have he : (π ^ m * unitsModRep t)⁻¹ * r = (unitsModRep t)⁻¹ * (π ^ (-m) * r) := by
      rw [mul_inv_rev, zpow_neg, mul_assoc]
    have hs := sub_mem_of_inv_mul_mem (hy t) (he ▸ hc)
    rw [hnm] at hs
    refine (hR2 _ (hy t)).unique (hg t) ⟨hr, ?_⟩
    rw [← neg_sub]
    exact neg_mem hs
  · intro t _
    have h := term_eq hψ hψ1 hχ hr (hy t) (z := g t) (by rw [← neg_sub]; exact neg_mem (hg t).2)
    exact h.symm

end GlobalTheory.DelEps.GaussBridge

open GlobalTheory.DelEps.GaussBridge in

theorem GlobalTheory.DelEps.tateEps_eq_localEpsilon_half : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Continuous ψ →
    ψ ≠ 1 → ∀ χ : Fˣ →* ℂˣ, IsSmoothChar χ → tateEps ψ χ = GroundTheory.LocalField.localEpsilon χ ψ (1 / 2) := by
  intro F _ _ _ _ _ _ ψ hψ hψ1 χ hχ
  obtain ⟨hq, hord, hun, hexp, hcond⟩ := GlobalTheory.DelGlob.localVocabularyDictionary F
  obtain ⟨h1, -⟩ := GlobalTheory.DelEps.isTateEps_tateEps_and_ne_zero F ψ hψ hψ1 χ hχ
  obtain ⟨c, a, R, hc, ha, hR, he⟩ := h1
  have hχc := continuous_of_isSmoothChar hχ
  have hcord : GroundTheory.LocalField.ord (c : F) = GroundTheory.LocalField.addCharConductor ψ := by
    rw [hcond ψ c hc, hord c]
  have ha' := hexp χ a ha
  by_cases hu : GroundTheory.LocalField.IsUnramifiedChar χ
  · have e1 : tateEps ψ χ = (((χ c)⁻¹ : ℂˣ) : ℂ) :=
      IsTateEps.unique ⟨c, a, R, hc, ha, hR, he⟩ (isTateEps_of_isUnram hc ((hun χ).2 hu))
    rw [e1, GroundTheory.LocalField.localEpsilon_of_isUnramified hu, sub_self, mul_zero, Complex.cpow_zero,
      mul_one]
    set π := GroundTheory.LocalField.unifUnit F
    set N := GroundTheory.LocalField.addCharConductor ψ
    have hw : π ^ (-N) * c ∈ GroundTheory.LocalField.unitFiltrationUnits F 0 := by
      rw [GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff_ord, GroundTheory.LocalField.ord_units_mul,
        GroundTheory.LocalField.ord_unifUnit_zpow, hcord]
      ring
    have hk : χ (π ^ (-N) * c) = 1 := hu hw
    have hχc' : χ c = χ π ^ N := by
      have e : c = π ^ N * (π ^ (-N) * c) := by rw [zpow_neg, mul_inv_cancel_left]
      rw [e, map_mul, hk, mul_one, map_zpow]
    rw [hχc', Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, zpow_neg]
  · rw [he, GroundTheory.LocalField.localEpsilon_eq_gaussSum hψ hψ1 hχc hu, hq, ← ha']
    have hR1 : ∀ r ∈ R, GroundTheory.LocalField.ord (r : F) =
        GroundTheory.LocalField.addCharConductor ψ - GroundTheory.LocalField.quasiCharConductor χ := by
      intro r hr
      rw [← hord, hR.1 r hr, hord, hcord, ha']
    have hR2 : ∀ y : Fˣ, GroundTheory.LocalField.ord (y : F) =
        GroundTheory.LocalField.addCharConductor ψ - GroundTheory.LocalField.quasiCharConductor χ →
        ∃! r : Fˣ, r ∈ R ∧ (y : F) - r ∈ GroundTheory.LocalField.valBall F (GroundTheory.LocalField.addCharConductor ψ) := by
      intro y hy
      have := hR.2 y (by rw [hord, hord, hy, hcord, ha'])
      simp only [valuation_le_iff_mem_valBall, hcord] at this
      exact this
    rw [← sum_shellReps_eq_gaussSum hψ hψ1 hχc hu hR1 hR2]
    congr 1
    · congr 1
      push_cast
      ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [Units.val_inv_eq_inv_val]

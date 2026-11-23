import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.RedRules

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (σ : Type)

theorem inj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
  IsFractionRing.injective _ _

theorem coeff_smul' (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (α : σ →₀ ℕ) :
    coeff α (r • f) = algebraMap _ (Fr p k) r * coeff α f := by
  change r • coeff α f = _
  rw [Algebra.smul_def]

theorem intBy_one_iff (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨fun α => WittVector.constantCoeff (w α), fun α => ⟨w α, ?_, rfl⟩⟩
    rw [hw α, one_mul]
  · rintro ⟨g, hg⟩ α
    obtain ⟨w, hw, -⟩ := hg α
    exact ⟨w, by rw [one_mul, hw]⟩

theorem red_unique (f : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f g') : g = g' := by
  ext α
  obtain ⟨w, hw, hg⟩ := h α
  obtain ⟨w', hw', hg'⟩ := h' α
  have : w = w' := inj p k (hw.symm.trans hw')
  rw [← hg, ← hg', this]

theorem red_lift (g : MvPowerSeries σ k) : Red p (Katz.lift p g) g := fun α =>
  ⟨WittVector.teichmuller p (coeff α g), coeff_lift p g α, by
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

theorem red_add_sub (f f' : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f' g') : Red p (f + f') (g + g') ∧ Red p (f - f') (g - g') := by
  constructor
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w + w', by rw [map_add, map_add, hw, hw'], by rw [map_add, map_add, hg, hg']⟩
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w - w', by rw [map_sub, map_sub, hw, hw'], by rw [map_sub, map_sub, hg, hg']⟩

theorem red_smul (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (g : MvPowerSeries σ k)
    (h : Red p f g) : Red p (r • f) (WittVector.constantCoeff r • g) := by
  intro α
  obtain ⟨w, hw, hg⟩ := h α
  refine ⟨r * w, ?_, ?_⟩
  · rw [coeff_smul', hw, map_mul]
  · rw [map_mul, hg, MvPowerSeries.coeff_smul]

theorem constantCoeff_p_mul (v : WittVector p k) :
    WittVector.constantCoeff ((p : WittVector p k) * v) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem exists_p_mul [PerfectRing k p] (w : WittVector p k) (hw : WittVector.constantCoeff w = 0) :
    ∃ v, w = (p : WittVector p k) * v := by
  by_cases h0 : w = 0
  · exact ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  cases m with
  | zero =>
    rw [pow_zero, one_mul, WittVector.constantCoeff_apply] at hw
    exact absurd hw hb
  | succ m => exact ⟨(p : WittVector p k) ^ m * b, by rw [pow_succ, mul_comm _ (p : WittVector p k), mul_assoc]⟩

theorem intBy_p_iff [PerfectRing k p] (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ p ↔ Red p f 0 := by
  constructor
  · intro hf α
    obtain ⟨v, hv⟩ := hf α
    exact ⟨_, hv, by rw [constantCoeff_p_mul, map_zero]⟩
  · intro hf α
    obtain ⟨w, hw, h0⟩ := hf α
    rw [map_zero] at h0
    obtain ⟨v, rfl⟩ := exists_p_mul p k w h0
    exact ⟨v, hw⟩

theorem intBy_iff (c : WittVector p k) (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨(fun α => algebraMap _ (Fr p k) (w α) : MvPowerSeries σ (Fr p k)), fun α => ⟨w α, by rw [one_mul]; rfl⟩, ?_⟩
    ext α
    rw [hw α, map_mul]
    exact (coeff_smul' p k σ c (fun α => algebraMap _ (Fr p k) (w α)) α).symm
  · rintro ⟨g, hg, rfl⟩ α
    obtain ⟨w, hw⟩ := hg α
    exact ⟨w, by rw [coeff_smul', hw, one_mul, map_mul]⟩

end GlobalTheory.Katz.RedRules

open GlobalTheory.Katz.RedRules in
theorem GlobalTheory.Katz.red_rules : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ : Type), (∀ (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g) ∧ (∀ (f : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f g' → g = g') ∧ (∀ g : MvPowerSeries σ k, Red p (Katz.lift p g) g) ∧ (∀ (f f' : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f' g' → Red p (f + f') (g + g') ∧ Red p (f - f') (g - g')) ∧ (∀ (r : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)) g, Red p f g → Red p (r • f) (WittVector.constantCoeff r • g)) ∧ (∀ f : MvPowerSeries (σ) (Fr p k), f ∈ intBy p k σ p ↔ Red p f 0) ∧ (∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g) := by
  intro p _ k _ _ _ σ
  exact ⟨intBy_one_iff p k σ, red_unique p k σ, red_lift p k σ, red_add_sub p k σ, red_smul p k σ,
    intBy_p_iff p k σ, intBy_iff p k σ⟩

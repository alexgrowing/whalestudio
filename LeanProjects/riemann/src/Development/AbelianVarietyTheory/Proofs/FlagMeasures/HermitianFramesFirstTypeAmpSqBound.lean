import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasicInequality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFiniteStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FirstType

theorem geom_le (x : ℝ) (hx : 2 ≤ x) (n : ℕ) : ∑ i ∈ Finset.range (n + 1), x ^ i ≤ 2 * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 0 ≤ x ^ n := by positivity
    nlinarith

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem mass_le_sum (S : Frames L r k) (d : S.Datum) (P : Submodule L.O S.V → Prop) {ι : Type}
    (s : Finset ι) (Q : ι → Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ i ∈ s, Q i Λ) : S.mass d P ≤ ∑ i ∈ s, S.mass d (Q i) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  · obtain ⟨i, hi, hq⟩ := h _ ho.1 ho.2
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) hi)
    rw [if_pos ⟨ho.1, hq⟩]
  · exact zero_le

theorem mass_mono (S : Frames L r k) (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  simpa using mass_le_sum S d P ({()} : Finset Unit) (fun _ => Q) (fun Λ _ hp => ⟨(), by simp, h Λ hp⟩)

theorem first_type_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ ENNReal.ofReal (2 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * (S.q : ℝ) ^ (-((k : ℤ) - 1))) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hamp, hbasic⟩ := BasicIneq.basic_inequality L r k S hk1
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hqR : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
  have hH : 0 ≤ S.Hp := by unfold Frames.Hp; positivity
  set A₀ : ℝ := S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA₀
  set A₁ : ℝ := 4 * S.Hp ^ (4 * (r + 1)) with hA₁
  have hA0 : 0 ≤ A₀ := by positivity
  have hA1 : 0 ≤ A₁ := by positivity
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β
  · obtain ⟨d₀, Λ₀, ht₀, hb₀, -, hβ₀⟩ := hex
    obtain ⟨-, -, -, -, -, ⟨m, -, hm⟩, hiff, -⟩ := Defect.exponents_and_defect L r k S d₀ Λ₀ ht₀
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
      rcases m with _ | n
      · exact absurd (hiff.2 (by simpa using hm)) hb₀
      · exact ⟨n, rfl⟩
    have hβ : β = S.q ^ (n + 1) := hβ₀ ▸ hm
    obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
    have hx : (2 : ℝ) ≤ (S.q : ℝ) ^ e := by
      have : (S.q : ℝ) ^ 1 ≤ (S.q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) (by omega)
      rw [pow_one] at this
      linarith
    have hmass : ∀ d, S.mass d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤
        ENNReal.ofReal (A₀ * (2 * ((S.q : ℝ) ^ e) ^ n)) := by
      intro d
      refine (mass_le_sum S d _ (Finset.range (n + 1)) (fun i Λ => S.cardI d Λ = S.q ^ i) ?_).trans ?_
      · rintro Λ ht ⟨h1, h2, h3⟩
        obtain ⟨⟨i, hi⟩, -, hle⟩ := SmallImage.small_image L r (e + 1) S d Λ ht
        have h4 := hle h1 h2
        rw [hi, h3, hβ, ← pow_succ'] at h4
        have := (Nat.pow_le_pow_iff_right (by omega)).1 h4
        exact ⟨i, Finset.mem_range.2 (by omega), hi⟩
      · refine (Finset.sum_le_sum fun i _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r (e + 1) S hk1 d).1 (S.q ^ i)).trans ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hA0
        refine le_trans (le_of_eq ?_) (geom_le _ hx n)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.add_sub_cancel, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm]
    have h1 := hbasic (fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) _ 1 zero_le_one hmass
      (fun d => by simpa using hamp d _)
    have h2 : (S.sumData fun d => S.mass d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β)) ≤
        S.sumData fun d => S.mass d fun Λ => S.be d Λ = β := by
      unfold Frames.sumData
      refine ENNReal.tsum_le_tsum fun o => ?_
      gcongr
      exact mass_mono S _ _ _ fun Λ h => h.2.2
    have h3 := GlobalTheory.T.sumData_mass_be_eq_le L r (e + 1) S hk β (by rw [hβ]; exact Nat.one_le_pow _ _ (by omega))
    refine h1.trans ((mul_le_mul_right (h2.trans h3) _).trans (le_of_eq ?_))
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have hq0 : (S.q : ℝ) ≠ 0 := by positivity
    have : (-(((e + 1 : ℕ) : ℤ) - 1)) = -(e : ℤ) := by push_cast; ring
    rw [this, zpow_neg, zpow_natCast, hβ, Nat.add_sub_cancel, Nat.cast_pow, ← hA₁]
    field_simp
    ring
  · have hmass : ∀ d, S.mass d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤
        ENNReal.ofReal 0 := by
      intro d
      simpa using mass_le_sum S d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β)
        (∅ : Finset Unit) (fun _ _ => True) (fun Λ ht hp => absurd ⟨d, Λ, ht, hp⟩ hex)
    have h1 := hbasic (fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) _ 1 zero_le_one hmass
      (fun d => by simpa using hamp d _)
    refine h1.trans ?_
    simp

end GlobalTheory.HL.FirstType

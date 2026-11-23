import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasicInequality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeCardMulSum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFiniteStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NoCancellation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem mass_le_sum {ι : Type} (s : Finset ι) (d : S.Datum) (P : Submodule L.O S.V → Prop)
    (Q : ι → Submodule L.O S.V → Prop) (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ i ∈ s, Q i Λ) :
    S.mass d P ≤ ∑ i ∈ s, S.mass d (Q i) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases hP : S.IsTerm d o.out ∧ P o.out
  · obtain ⟨i, hi, hQ⟩ := h _ hP.1 hP.2
    rw [if_pos hP]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => if S.IsTerm d o.out ∧ Q i o.out then
      ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => zero_le) hi)
    exact (if_pos ⟨hP.1, hQ⟩).ge
  · rw [if_neg hP]
    exact zero_le

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem mass_mono (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  simpa using mass_le_sum S {()} d P (fun _ => Q) (fun Λ h1 h2 => ⟨(), by simp, h Λ h1 h2⟩)

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem sumData_mass_le (P : S.Datum → Submodule L.O S.V → Prop) :
    (S.sumData fun d => S.mass d (P d)) ≤ S.nn := by
  unfold Frames.nn Frames.sumData
  exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (mass_mono S _ _ _ fun _ _ _ => trivial) _

theorem ampSq_le_of_mass (hk : 1 ≤ k) (P : S.Datum → Submodule L.O S.V → Prop) (B : ℝ)
    (hB : ∀ d, S.mass d (P d) ≤ ENNReal.ofReal B) :
    S.ampSq P ≤ ENNReal.ofReal B * S.sumData fun d => S.mass d (P d) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk
  simpa using h2 P B 1 zero_le_one hB (fun d => by simpa using h1 d (P d))

theorem ampSq_le_of_zero (hk : 1 ≤ k) (P : S.Datum → Submodule L.O S.V → Prop)
    (hP : ∀ d Λ, S.IsTerm d Λ → P d Λ → S.BBzero d Λ) :
    S.ampSq P ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn := by
  refine (ampSq_le_of_mass S hk P _ fun d => ?_).trans
    (mul_le_mul_right (sumData_mass_le S P) _)
  by_cases hT : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hT
    have hH : 1 ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀).2.2.2.2.1
    have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
    refine (mass_mono S d _ (fun Λ => S.cardI d Λ = 1) fun Λ h1 h2 => ?_).trans
      (((GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk d).1 1).trans (ENNReal.ofReal_le_ofReal ?_))
    · have hb := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h1).2.2.2.2.2.2.1.1 (hP d Λ h1 h2)
      obtain ⟨⟨i, hi⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ h1
      have : 0 < S.q ^ i := by positivity
      omega
    · rw [Nat.cast_one, one_pow, mul_one]
      exact pow_le_pow_right₀ hH (by nlinarith)
  · refine (mass_le_sum S (∅ : Finset Unit) d _ (fun _ _ => True) fun Λ h1 _ =>
      (hT ⟨Λ, h1⟩).elim).trans ?_
    simp

theorem ampSq_defect_le (hk : 4 * r + 7 ≤ k) (hH : 0 ≤ S.Hp) (i : ℕ) :
    (S.ampSq fun d Λ => S.be d Λ = S.q ^ i) ≤
      ENNReal.ofReal ((i + 1) * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
        (4 * S.Hp ^ (4 * (r + 1)))) * S.nn := by
  have hk1 : 1 ≤ k := by omega
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hβ : 0 < S.q ^ i := by positivity
  have hβ' : (0 : ℝ) < ((S.q ^ i : ℕ) : ℝ) ^ (k - 1) := by positivity
  have hm : ∀ d, S.mass d (fun Λ => S.be d Λ = S.q ^ i) ≤ ENNReal.ofReal ((i + 1) *
      (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((S.q ^ i : ℕ) : ℝ) ^ (k - 1))) := by
    intro d
    refine (mass_le_sum S (Finset.range (i + 1)) d _ (fun j Λ => S.cardI d Λ = S.q ^ j)
      fun Λ h1 h2 => ?_).trans ?_
    · obtain ⟨⟨j, hj⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ h1
      refine ⟨j, Finset.mem_range.2 ?_, hj⟩
      rw [hj, h2] at hle
      have := (Nat.pow_le_pow_iff_right (by omega)).1 hle
      omega
    · refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal
        (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((S.q ^ i : ℕ) : ℝ) ^ (k - 1)))
        fun j hj => ?_).trans ?_
      · refine ((GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).1 _).trans (ENNReal.ofReal_le_ofReal ?_)
        have hji : S.q ^ j ≤ S.q ^ i :=
          Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.1 hj; omega)
        gcongr
      · rw [Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ i + 1),
          ← ENNReal.ofReal_natCast, Nat.cast_succ]
  refine (ampSq_le_of_mass S hk1 _ _ hm).trans ?_
  refine (mul_le_mul_right (GlobalTheory.T.sumData_mass_be_eq_le L r k S hk _ hβ) _).trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

theorem ampSq_le_height_mul_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → S.ampSq S.BBzero ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn ∧ (S.ampSq fun _ _ => True) ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk
  have hk1 : 1 ≤ k := by omega
  refine ⟨ampSq_le_of_zero S hk1 _ fun _ _ _ h => h, ?_⟩
  by_cases hz : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ
  · exact ampSq_le_of_zero S hk1 _ fun d Λ h _ => hz d Λ h
  push_neg at hz
  obtain ⟨d₀, Λ₀, h₀, hn⟩ := hz
  obtain ⟨ha, -, -, hqa, hH, -, -, hqH, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ h₀
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq' : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
  have h2 : (2 : ℝ) ≤ S.Hp := hq'.trans (hqH hn)
  obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le ha
  have hAH : (A : ℝ) + 1 ≤ S.Hp := by
    rw [hA, zpow_natCast] at hqa
    have h1 : A + 1 ≤ S.q ^ A := Nat.lt_pow_self (by omega)
    exact le_trans (by exact_mod_cast h1) hqa
  refine (GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 (Finset.range (A + 1))
    (fun i d Λ => S.be d Λ = S.q ^ i) _ (fun d Λ h => ?_) (fun d Λ h i _ i' _ h1 h2 => ?_)).trans ?_
  · obtain ⟨i, hi, hb⟩ := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.2.1
    exact ⟨fun _ => ⟨i, Finset.mem_range.2 (by omega), hb⟩, fun _ => trivial⟩
  · exact Nat.pow_right_injective hq (h1.symm.trans h2)
  have hsum := Finset.sum_le_card_nsmul (Finset.range (A + 1))
    (fun i => S.ampSq fun d Λ => S.be d Λ = S.q ^ i)
    (ENNReal.ofReal (S.Hp * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
        (S.Hp ^ 2 * S.Hp ^ (4 * (r + 1)))) * S.nn) (fun i hi => by
      refine (ampSq_defect_le S hk (by linarith) i).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
      have hi' : (i : ℝ) ≤ A := by
        have := Finset.mem_range.1 hi
        exact_mod_cast (by omega : i ≤ A)
      have h4 : (4 : ℝ) ≤ S.Hp ^ 2 := by nlinarith
      have h5 : (i : ℝ) + 1 ≤ S.Hp := by linarith
      gcongr)
  refine (mul_le_mul_right hsum _).trans ?_
  have hc : ((A + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal S.Hp := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact hAH)
  rw [Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  refine (mul_le_mul_left (mul_le_mul' hc hc) _).trans ?_
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have he : S.Hp * S.Hp * (S.Hp * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
      (S.Hp ^ 2 * S.Hp ^ (4 * (r + 1)))) = S.Hp ^ (9 * (r + 1) ^ 2 + 16 * (r + 1) + 5) := by
    ring
  rw [he]
  exact pow_le_pow_right₀ hH (by nlinarith)

end GlobalTheory.HL.NoCancellation

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

theorem one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (g h : ι → ℝ)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1) (hgh : ∀ i, 1 - g i ≤ h i) :
    1 - ∏ i ∈ s, g i ≤ ∑ i ∈ s, h i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hP0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i _ => hg0 i
    have hP1 : ∏ i ∈ s, g i ≤ 1 := Finset.prod_le_one (fun i _ => hg0 i) fun i _ => hg1 i
    have key : 1 - g a * ∏ i ∈ s, g i = (1 - ∏ i ∈ s, g i) + (1 - g a) * ∏ i ∈ s, g i := by ring
    have h1 : (1 - g a) * ∏ i ∈ s, g i ≤ 1 - g a :=
      mul_le_of_le_one_right (by linarith [hg1 a]) hP1
    linarith [hgh a]

theorem raiseSmall_factor {f : ℕ} (N j' : ℕ) (x : Fin f → Fin N → ℝ) (δ : ℝ)
    (hx : ∀ τ (i l : Fin N), i < l → x τ l < x τ i) (τ : Fin f) (i l : Fin N) :
    (if i < l then raiseSmall N j' δ x τ i - raiseSmall N j' δ x τ l else 1) =
      (if i < l then x τ i - x τ l else 1) *
        (if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1) := by
  by_cases hil : i < l
  · have hpos : 0 < x τ i - x τ l := sub_pos.mpr (hx τ i l hil)
    have hlt : i.val < l.val := hil
    simp only [if_pos hil, raiseSmall]
    by_cases hA : Across N j' i l
    · obtain ⟨h1, h2⟩ := hA
      have hi : ¬ N - j' ≤ i.val := by omega
      rw [if_neg hi, if_pos h2, if_pos (show Across N j' i l from ⟨h1, h2⟩)]
      field_simp
      ring
    · rw [if_neg hA, mul_one]
      simp only [Across, not_and, not_le] at hA
      by_cases hi : N - j' ≤ i.val
      · rw [if_pos hi, if_pos (show N - j' ≤ l.val by omega)]; ring
      · have hl := hA (by omega)
        rw [if_neg hi, if_neg (show ¬ N - j' ≤ l.val by omega)]
  · have hA : ¬ Across N j' i l := by
      rintro ⟨h1, h2⟩
      exact hil (Fin.lt_def.mpr (by omega))
    simp [hil, hA]

theorem DegreeRatio.proof : DegreeRatio.Statement := by
  intro f N j' x δ ⟨hδ, hx, hacross⟩
  set P : Fin f → Fin N → Fin N → ℝ :=
    fun τ i l => if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1 with hPdef
  set H : Fin f → Fin N → Fin N → ℝ :=
    fun τ i l => if Across N j' i l then δ / (x τ i - x τ l) else 0 with hHdef

  have hfac : ∀ τ (i l : Fin N), 0 < (if i < l then x τ i - x τ l else 1) := by
    intro τ i l
    split_ifs with h
    · exact sub_pos.mpr (hx τ i l h)
    · exact one_pos
  have hdeg : 0 < weightDegree x :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => hfac τ i l

  have hP0 : ∀ τ i l, 0 < P τ i l := by
    intro τ i l
    simp only [hPdef]
    split_ifs with hA
    · have hd := hacross τ i l hA
      have hpos : 0 < x τ i - x τ l := by linarith
      have : δ / (x τ i - x τ l) < 1 := (div_lt_one hpos).mpr hd
      linarith
    · exact one_pos
  have hP1 : ∀ τ i l, P τ i l ≤ 1 := by
    intro τ i l
    simp only [hPdef]
    split_ifs with hA
    · have hd := hacross τ i l hA
      have : 0 ≤ δ / (x τ i - x τ l) := div_nonneg hδ (by linarith)
      linarith
    · exact le_rfl
  have hPH : ∀ τ i l, 1 - P τ i l ≤ H τ i l := by
    intro τ i l
    simp only [hPdef, hHdef]
    split_ifs <;> simp

  have hratio : weightDegree (raiseSmall N j' δ x) / weightDegree x = ∏ τ, ∏ i, ∏ l, P τ i l := by
    rw [div_eq_iff hdeg.ne']
    simp only [weightDegree, raiseSmall_factor N j' x δ hx, Finset.prod_mul_distrib, hPdef]
    ring
  rw [hratio]
  have hin0 : ∀ τ i, 0 ≤ ∏ l, P τ i l := fun τ i => Finset.prod_nonneg fun l _ => (hP0 τ i l).le
  have hin1 : ∀ τ i, ∏ l, P τ i l ≤ 1 :=
    fun τ i => Finset.prod_le_one (fun l _ => (hP0 τ i l).le) fun l _ => hP1 τ i l
  have hmid0 : ∀ τ, 0 ≤ ∏ i, ∏ l, P τ i l := fun τ => Finset.prod_nonneg fun i _ => hin0 τ i
  have hmid1 : ∀ τ, ∏ i, ∏ l, P τ i l ≤ 1 :=
    fun τ => Finset.prod_le_one (fun i _ => hin0 τ i) fun i _ => hin1 τ i
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => hP0 τ i l
  · exact Finset.prod_le_one (fun τ _ => hmid0 τ) fun τ _ => hmid1 τ
  · refine one_sub_prod_le_sum _ _ _ hmid0 hmid1 fun τ => ?_
    refine one_sub_prod_le_sum _ _ _ (hin0 τ) (hin1 τ) fun i => ?_
    exact one_sub_prod_le_sum _ _ _ (fun l => (hP0 τ i l).le) (hP1 τ i) (hPH τ i)

end GroundTheory.Heights₂.Heights.FourB

import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.VdFormula
import Development.AutomorphicArithmetic.FrobeniusLocalisation.LayerBot

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.mem_ram :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → (l ∈ H.ram ↔ H.el l ≠ 1) ∧ (l ∈ H.ram ↔ l ∣ H.condE) ∧ (l ∈ H.ram ↔ H.vdH l ≠ 0) ∧ (l ∈ H.ram → 1 / 2 ≤ H.vdH l) ∧ (l ∈ H.ram → 1 - 1 / (H.el l : ℝ) ≤ H.vdH l) := by
  intro φ H l hl
  haveI : Fact l.Prime := ⟨hl⟩
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  obtain ⟨hE, hEpos, _⟩ := condE_spec H.toHostRaw
  set v := H.condN.factorization l with hv
  set e := H.condE.factorization l with he
  have hlay := fun j (hj : j ≤ v) => layer_bot H.toHostRaw hl hj
  have hev : e ≤ v := ((hlay 0 (Nat.zero_le _)).2.2)
  have hcardbot : ∀ j, j ≤ v →
      (Nat.card (H.imgOne (H.condN / l ^ v * l ^ j)) = 1 ↔ e ≤ j) := by
    intro j hj
    rw [Subgroup.card_eq_one]
    exact (hlay j hj).1
  have hdvdE : l ∣ H.condE ↔ 0 < e := by
    rw [he]
    exact hl.dvd_iff_one_le_factorization hEpos.ne'
  have hel : H.el l = Nat.card (H.imgOne (H.condN / l ^ v * l ^ 0)) := by
    simp [HostRaw.el, HostRaw.inertG, hv]
  have hA : H.el l ≠ 1 ↔ l ∣ H.condE := by
    rw [hel, Ne, hcardbot 0 (Nat.zero_le _), hdvdE]
    omega
  have hT : ∀ n : ℕ, 0 ≤ 1 - 1 / (n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
      have : 1 / (n : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact h1
      linarith
  have hT0 : ∀ n : ℕ, (1 - 1 / (n : ℝ) = 0 ↔ n = 1) := by
    intro n
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · simp [h0] at h
      · have hn : (n : ℝ) ≠ 0 := by positivity
        have : (n : ℝ) = 1 := by
          field_simp at h
          linarith
        exact_mod_cast this
    · intro h
      simp [h]
  have hB : H.vdH l ≠ 0 ↔ l ∣ H.condE := by
    rw [vd_formula H hl, Ne, Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hT _), hdvdE]
    constructor
    · intro h
      by_contra h0
      apply h
      intro j hj
      rw [hT0, hcardbot j (Finset.mem_range.1 hj).le]
      omega
    · intro h hall
      have h0 := hall 0 (Finset.mem_range.2 (lt_of_lt_of_le h hev))
      rw [hT0, hcardbot 0 (Nat.zero_le _)] at h0
      omega
  have hC : l ∈ H.ram ↔ H.vdH l ≠ 0 := by
    have hd : (NumberField.discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.E)
    have hr : (Module.finrank ℚ H.E : ℝ) ≠ 0 := by
      have := Module.finrank_pos (R := ℚ) (M := H.E)
      positivity
    have key := dvd_iff_padicValNat_ne_zero (p := l) hd
    simp only [HostRaw.ram, Nat.mem_primeFactors, HostRaw.vdH, Ne, div_eq_zero_iff, hr, or_false,
      Nat.cast_eq_zero]
    rw [Ne] at key
    rw [← key]
    tauto
  have hlow : l ∈ H.ram → 1 - 1 / (H.el l : ℝ) ≤ H.vdH l := by
    intro hram
    have hpos : 0 < e := hdvdE.1 (hB.1 (hC.1 hram))
    rw [vd_formula H hl, hel]
    exact Finset.single_le_sum (f := fun j => 1 - 1 / (Nat.card (H.imgOne (H.condN / l ^ v * l ^ j)) : ℝ))
      (fun j _ => hT _) (Finset.mem_range.2 (lt_of_lt_of_le hpos hev))
  refine ⟨hC.trans (hB.trans hA.symm), hC.trans hB, hC, fun hram => ?_, hlow⟩
  have h2 : 2 ≤ H.el l := by
    have h1 := (hC.trans (hB.trans hA.symm)).1 hram
    have := HostRaw.el_pos H.toHostRaw l
    omega
  have h2r : (2 : ℝ) ≤ H.el l := by exact_mod_cast h2
  have hq : 1 / (H.el l : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2r
  linarith [hlow hram]

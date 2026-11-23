import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.FormalDegreeRatio

theorem thrStar_lt {N : ℕ} (ε : Fin N → Bool) {M : ℝ} (hNM : (N : ℝ) ≤ M) (hM : 1 ≤ M) :
    ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < 1000 * M ^ 3 - 1 := by
  have hp : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ M := by
    have : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ N := by
      unfold ReciprocityTheory.ChartRestriction.DS.pOf
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact le_trans (by exact_mod_cast this) hNM
  have hq : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ M := by
    have : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ N := by
      unfold ReciprocityTheory.ChartRestriction.DS.qOf
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact le_trans (by exact_mod_cast this) hNM
  have hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ M := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := min_le_right _ _
    exact le_trans (by exact_mod_cast this) hq
  have hq00 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := Nat.cast_nonneg _
  have hs : Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) ≤ 2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 1 := by
    calc Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))
        ≤ Real.sqrt ((2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 1 := Real.sqrt_sq (by linarith)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := Nat.cast_nonneg _
  have hqq0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := Nat.cast_nonneg _
  have h1 : (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ M * M * M := by
    gcongr
  have h2 : 16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ 16 * M * M := by
    gcongr
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM3 : M ^ 2 ≤ M ^ 3 := by nlinarith
  have hMM : M * M * M = M ^ 3 := by ring
  have hMM2 : 16 * M * M = 16 * M ^ 2 := by ring
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar
  have hmax : max ((N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1)
      (16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))) <
      1000 * M ^ 3 - 2 := by
    refine max_lt ?_ ?_
    · nlinarith
    · nlinarith
  linarith

theorem fdeg_const (N : ℕ) (ε : Fin N → Bool) : ∃ c : ℝ, 0 < c ∧ ∀ (lam : Fin N → ℝ) (h : ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h → ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h →
    (∃ a, ε a = true) → (∃ a, ε a = false) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat N → (H →L[ℂ] H)),
      Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) σ (c * Formalism.QuantumDeterminants.fdegHC lam) := by
  obtain ⟨c, hc, hF⟩ := ReciprocityTheory.ChartRestriction.DS.fdCons_muG N ε
  refine ⟨c, hc, fun lam h hlam hgap hh ht hf H _ _ σ hσ => ?_⟩
  have : CompleteSpace H := hσ.1
  have : Nontrivial H := hσ.2.1
  have hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by
    obtain ⟨a, ha⟩ := ht
    unfold ReciprocityTheory.ChartRestriction.DS.pOf
    exact Finset.card_pos.2 ⟨a, by simpa using ha⟩
  have hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := by
    obtain ⟨a, ha⟩ := hf
    unfold ReciprocityTheory.ChartRestriction.DS.qOf
    exact Finset.card_pos.2 ⟨a, by simpa using ha⟩
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := le_min hp hq
  have h8 : 8 * (N : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε < h := ReciprocityTheory.ChartRestriction.DS.fdc_eight hh
  have hΨ : ∀ μ : Fin N → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast ε μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε (ReciprocityTheory.ChartRestriction.DS.lowK ε μ))
        (Ψ : Matrix (Fin N) (Fin N) ℂ → (T.V →L[ℂ] T.V)), ReciprocityTheory.ChartRestriction.DS.IsPsiFor ε μ T Ψ := by
    intro μ hμ hgμ
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists ε μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor _ _ μ h T m hμ hm hgμ hq0 h8).1⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hval := hF lam H σ v hlam hσ h hgap hh hp hq hΨ hv
  obtain ⟨d, hd⟩ := ReciprocityTheory.ChartRestriction.DS.fdcGood_of_isDS hσ
  have := ReciprocityTheory.ChartRestriction.DS.muCD_isHaar ε
  have hs := Measure.haarScalarFactor_pos_of_isHaarMeasure (Formalism.REAL.muG ε) (ReciprocityTheory.ChartRestriction.DS.muCD ε)
  have heq := Measure.isMulLeftInvariant_eq_smul (Formalism.REAL.muG ε) (ReciprocityTheory.ChartRestriction.DS.muCD ε)
  have hc' : (0 : ℝ) < (Measure.haarScalarFactor (Formalism.REAL.muG ε) (ReciprocityTheory.ChartRestriction.DS.muCD ε) : ℝ) := by
    exact_mod_cast hs
  obtain ⟨s, hs0, hEq⟩ : ∃ s : ℝ, 0 < s ∧ Formalism.REAL.muG ε = ENNReal.ofReal s • ReciprocityTheory.ChartRestriction.DS.muCD ε :=
    ⟨_, hc', by rw [ENNReal.ofReal_coe_nnreal]; exact heq⟩
  have hd2 := ReciprocityTheory.ChartRestriction.DS.isFdeg_smul hs0 hd
  rw [← hEq] at hd2
  have e : d / s = c * Formalism.QuantumDeterminants.fdegHC lam := by
    rw [← ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' hd2 hv]
    exact hval
  rwa [e] at hd2

theorem isHCParam_sub {N : ℕ} {lam : Fin N → ℝ} (s : Fin N) (hl : Formalism.QuantumDeterminants.IsHCParam lam)
    (hw : ∀ a c, a < c → 2 ≤ lam a - lam c) : Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have := hw a b hab
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> linarith
  · obtain ⟨m, hm⟩ := hl.2 a
    by_cases ha : a = s
    · subst ha
      refine ⟨m - 1, ?_⟩
      simp only [Pi.sub_apply, Pi.single_eq_same]
      push_cast
      linarith
    · refine ⟨m, ?_⟩
      simp only [Pi.sub_apply, Pi.single_apply, if_neg ha]
      linarith

theorem gap_sub {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) (s : Fin N) {h : ℝ}
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) : Formalism.QuantumDeterminants.GapAtLeast ε (lam - Pi.single s 1) (h - 1) := by
  intro a b hab
  have h1 := hg a b hab
  have e : (lam - Pi.single s 1 : Fin N → ℝ) a - (lam - Pi.single s 1 : Fin N → ℝ) b =
      (lam a - lam b) - ((Pi.single s (1 : ℝ) : Fin N → ℝ) a - (Pi.single s (1 : ℝ) : Fin N → ℝ) b) := by
    simp only [Pi.sub_apply]; ring
  have ht : |(Pi.single s (1 : ℝ) : Fin N → ℝ) a - (Pi.single s (1 : ℝ) : Fin N → ℝ) b| ≤ 1 := by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have := abs_sub_abs_le_abs_sub (lam a - lam b) ((Pi.single s (1 : ℝ) : Fin N → ℝ) a - (Pi.single s (1 : ℝ) : Fin N → ℝ) b)
  rw [e]
  linarith

theorem fdegHC_le {N : ℕ} (lam : Fin N → ℝ) (s : Fin N) (hw : ∀ a c, a < c → 2 ≤ lam a - lam c) :
    Formalism.QuantumDeterminants.fdegHC lam ≤ 2 ^ (N - 1) * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1) := by
  set lam' := lam - Pi.single s 1 with hlam'
  have hfac : ∀ a b : Fin N, a < b → |lam a - lam b| ≤ (if a = s then (2 : ℝ) else 1) * |lam' a - lam' b| := by
    intro a b hab
    have hne : a ≠ b := hab.ne
    have h2 := hw a b hab
    by_cases ha : a = s
    · subst ha
      have e1 : lam' a = lam a - 1 := by simp [hlam']
      have e2 : lam' b = lam b := by simp [hlam', Pi.single_apply, hne.symm]
      rw [if_pos rfl, e1, e2, abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
    · rw [if_neg ha, one_mul]
      by_cases hb : b = s
      · subst hb
        have e1 : lam' a = lam a := by simp [hlam', Pi.single_apply, ha]
        have e2 : lam' b = lam b - 1 := by simp [hlam']
        rw [e1, e2, abs_of_pos (by linarith), abs_of_pos (by linarith)]
        linarith
      · have e1 : lam' a = lam a := by simp [hlam', Pi.single_apply, ha]
        have e2 : lam' b = lam b := by simp [hlam', Pi.single_apply, hb]
        rw [e1, e2]
  have hcount : ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (if a = s then (2 : ℝ) else 1) ≤
      2 ^ (N - 1) := by
    rw [Finset.prod_eq_single s (fun a _ ha => by simp [ha]) (fun h => absurd (Finset.mem_univ s) h)]
    simp only [if_pos rfl, Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num)
    have hsub : univ.filter (fun b : Fin N => s < b) ⊆ univ.erase s := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp [hb.ne']
    calc (univ.filter (fun b : Fin N => s < b)).card ≤ (univ.erase s).card := Finset.card_le_card hsub
      _ = N - 1 := by simp [Finset.card_erase_of_mem]
  have hnum : ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam a - lam b| ≤
      2 ^ (N - 1) * ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam' a - lam' b| := by
    calc ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam a - lam b|
        ≤ ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b),
            ((if a = s then (2 : ℝ) else 1) * |lam' a - lam' b|) :=
          Finset.prod_le_prod (fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _) fun a _ =>
            Finset.prod_le_prod (fun b _ => abs_nonneg _) fun b hb => hfac a b (Finset.mem_filter.1 hb).2
      _ = (∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (if a = s then (2 : ℝ) else 1)) *
            ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam' a - lam' b| := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_mul_distrib]
      _ ≤ 2 ^ (N - 1) * ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam' a - lam' b| :=
          mul_le_mul_of_nonneg_right hcount (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _)
  have hD : 0 < ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) :=
    Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => by
      have hab : a < b := (Finset.mem_filter.1 hb).2
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      linarith
  unfold Formalism.QuantumDeterminants.fdegHC
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hnum hD.le

theorem degRatio_holds : DegRatio := by
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ
  obtain ⟨i0, hi0⟩ := hP.neg
  have hε't : ∃ a, ε' a = true := by
    by_contra hne
    push_neg at hne
    have h1 := hP.pos
    have h0 : (univ.filter fun i => ε' i = true) = ∅ := by
      ext i
      simp [hne i]
    rw [h0, Finset.card_empty] at h1
    have : 0 < (univ.filter fun i => ε' i = false).card := Finset.card_pos.2 ⟨i0, by simp [hi0]⟩
    omega
  have hεt : ∃ a, ε a = true := ⟨e none, hP.signs.1⟩
  have hεf : ∃ a, ε a = false := ⟨e (some i0), by rw [hP.signs.2 i0]; exact hi0⟩
  obtain ⟨c, hc, hF⟩ := fdeg_const (n + 1) ε
  obtain ⟨c', -, hF'⟩ := fdeg_const n ε'
  have hM : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hthr : ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < 1000 * ((n : ℝ) + 1) ^ 3 - 1 :=
    thrStar_lt ε (by push_cast; exact le_refl _) hM
  have hthr' : ReciprocityTheory.ChartRestriction.DS.thrStar ε' + 1 < 1000 * ((n : ℝ) + 1) ^ 3 - 1 :=
    thrStar_lt ε' (by linarith) hM
  refine ⟨⟨c' * Formalism.QuantumDeterminants.fdegHC mu, hF' mu _ hP.hmu hP.gap' (by linarith) hε't ⟨i0, hi0⟩ H' σ hσ⟩,
    c * Formalism.QuantumDeterminants.fdegHC lam, hF lam _ hP.hlam hP.gap (by linarith) hεt hεf H π hπ, fun s K _ _ ρ hρ => ?_⟩
  refine ⟨c * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1),
    hF _ _ (isHCParam_sub s hP.hlam hP.wide) (gap_sub ε lam s hP.gap) hthr hεt hεf K ρ hρ, ?_⟩
  have h2 := fdegHC_le lam s hP.wide
  simp only [Nat.add_sub_cancel] at h2
  calc c * Formalism.QuantumDeterminants.fdegHC lam ≤ c * (2 ^ n * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1)) :=
        mul_le_mul_of_nonneg_left h2 hc.le
    _ = 2 ^ n * (c * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1)) := by ring

end GlobalTheory.SepReal.FormalDegreeRatio

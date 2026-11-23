import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiPart
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TauPart
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ByParts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiM
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.RhoEqRhoCAddRhoN

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

namespace InfKH

variable {Λ : Fin n → ℝ}

lemma lowMinusUp_expand {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) :
    lowMinusUp B = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
      ((if b < a then (1 : ℂ) else -1) * B a b) • Matrix.single a b (1 : ℂ) := by
  ext i j
  have hsum : (∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
      ((if b < a then (1 : ℂ) else -1) * B a b) • Matrix.single a b (1 : ℂ)) i j =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
        if a = i ∧ b = j then (if b < a then (1 : ℂ) else -1) * B a b else 0 := by
    first
    | simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
    | (simp only [Matrix.sum_apply]
       refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
       by_cases h : a = i ∧ b = j
       · rw [if_pos h]
         obtain ⟨rfl, rfl⟩ := h
         simp
       · rw [if_neg h]
         simp [Matrix.single_apply, h])
  rw [hsum]
  rw [Finset.sum_eq_single i (fun a _ ha => Finset.sum_eq_zero fun b _ => if_neg fun h => ha h.1)
    (fun h => absurd (Finset.mem_univ i) h)]
  by_cases hj : ε j = ε i ∧ j ≠ i
  · rw [Finset.sum_eq_single j (fun b _ hb => if_neg fun h => hb h.2)
      (fun h => (h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)).elim)]
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [lowMinusUp, Matrix.of_apply]
    rcases lt_trichotomy j i with h | h | h
    · simp [h]
    · exact absurd h hj.2
    · simp [h, not_lt.2 h.le]
  · rw [Finset.sum_eq_zero fun b hb => if_neg fun h => hj (by
      obtain ⟨-, rfl⟩ := h
      exact (Finset.mem_filter.1 hb).2)]
    simp only [lowMinusUp, Matrix.of_apply]
    by_cases he : j = i
    · subst he
      simp
    · have hne : ε i ≠ ε j := fun h => hj ⟨h.symm, he⟩
      simp [hB i j hne]

lemma isBlock_single {a b : Fin n} (h : ε b = ε a) : IsBlock ε (Matrix.single a b (1 : ℂ)) := by
  intro a' b' hne
  by_cases h' : a = a' ∧ b = b'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd h.symm hne
  · first
    | rw [Matrix.single_apply, if_neg h']
    | simp [Matrix.single_apply, h']
    | (simp only [Matrix.single_apply]
       exact if_neg h')

lemma scal (μ : Fin n → ℤ) (hμ : IsMu lam μ) (B : Matrix (Fin n) (Fin n) ℂ) :
    2 * ∑ a, (μ a : ℂ) * B a a =
      2 * ∑ a, ((lowK ε lam a : ℝ) : ℂ) * B a a + 4 * ∑ a, ((rhoC ε a : ℝ) : ℂ) * B a a := by
  have key : ∀ a, ((μ a : ℤ) : ℂ) = ((lowK ε lam a : ℝ) : ℂ) + 2 * ((rhoC ε a : ℝ) : ℂ) := by
    intro a
    have hgt1 : (univ.filter (fun b => a < b ∧ ε b = ε a)).card +
        (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card = (univ.filter (fun b => a < b)).card := by
      first
      | (have h1 := Finset.filter_card_add_filter_neg_card_eq_card
            (s := univ.filter (fun b => a < b)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
      | (have h1 := Finset.card_filter_add_card_filter_not
            (s := univ.filter (fun b => a < b)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
    have hlt1 : (univ.filter (fun b => b < a ∧ ε b = ε a)).card +
        (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card = (univ.filter (fun b => b < a)).card := by
      first
      | (have h1 := Finset.filter_card_add_filter_neg_card_eq_card
            (s := univ.filter (fun b => b < a)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
      | (have h1 := Finset.card_filter_add_card_filter_not
            (s := univ.filter (fun b => b < a)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
    have hc1 : (univ.filter (fun b : Fin n => a < b)).card + (a : ℕ) + 1 = n := by
      have ha := a.isLt
      first
      | (rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
         omega)
      | (simp only [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
         omega)
    have hc2 : (univ.filter (fun b : Fin n => b < a)).card = (a : ℕ) := by
      first
      | rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
      | simp [Finset.filter_gt_eq_Iio]
    have hr : ((μ a : ℤ) : ℝ) = lowK ε lam a + 2 * rhoC ε a := by
      rw [hμ a]
      delta lowK rhoC rhoN rho
      simp only [Pi.add_apply, Pi.sub_apply]
      have e1 : ((univ.filter (fun b => a < b ∧ ε b = ε a)).card : ℝ) +
          (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card + (a : ℕ) + 1 = n := by
        exact_mod_cast (hgt1.symm ▸ hc1 : _)
      have e2 : ((univ.filter (fun b => b < a ∧ ε b = ε a)).card : ℝ) +
          (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card = (a : ℕ) := by
        exact_mod_cast (hlt1.trans hc2)
      linarith
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) hr
    push_cast at h2 ⊢
    linear_combination h2
  have e : ∑ a, (μ a : ℂ) * B a a = ∑ a, ((lowK ε lam a : ℝ) : ℂ) * B a a +
      2 * ∑ a, ((rhoC ε a : ℝ) : ℂ) * B a a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a]
    ring
  rw [e]
  ring

def Ssum (T : KType ε Λ) (μ : Fin n → ℤ) (x A : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) : T.V →L[ℂ] T.V :=
  ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
    (if b < a then (1 : ℂ) else -1) • InfKA.Ek T μ x (InfKA.entryCLM a b) A (Matrix.single a b 1) k

lemma integral_Ssum [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) (A : Matrix (Fin n) (Fin n) ℂ) :
    Integrable (Ssum T μ x A) (muK ε) ∧ ∫ k, Ssum T μ x A k ∂(muK ε) = 0 := by
  have hI : ∀ a b : Fin n, Integrable (fun k => (if b < a then (1 : ℂ) else -1) •
      InfKA.Ek T μ x (InfKA.entryCLM a b) A (Matrix.single a b 1) k) (muK ε) := fun a b =>
    InfKA.integrable_of_cont ((InfKA.continuous_Ek T μ hx (InfKA.entryCLM a b) A
      (Matrix.single a b 1)).const_smul (if b < a then (1 : ℂ) else -1))
  refine ⟨integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hI a b, ?_⟩
  unfold Ssum
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hI a b]
  refine sum_eq_zero fun a _ => ?_
  rw [integral_finset_sum _ fun b _ => hI a b]
  refine sum_eq_zero fun b hb => ?_
  rw [integral_smul (if b < a then (1 : ℂ) else -1)
    (fun k => InfKA.Ek T μ x (InfKA.entryCLM a b) A (Matrix.single a b 1) k), InfKA.integral_Ek_block T μ hx _ A (isBlock_single (mem_filter.mp hb).2.1), smul_zero]

lemma Ssum_eq (T : KType ε Λ) (μ : Fin n → ℤ) (x A : Matrix (Fin n) (Fin n) ℂ) (k : KG ε)
    (hB : IsBlock ε (toMK k⁻¹ * A * toMK k)) :
    Ssum T μ x A k = InfKA.DkL T μ x k (lowMinusUp (toMK k⁻¹ * A * toMK k)) +
      (-4 * ∑ a, ((rhoC ε a : ℝ) : ℂ) * (toMK k⁻¹ * A * toMK k) a a) • Gint T μ x k := by
  have hφ : ∀ (a b : Fin n) (M : Matrix (Fin n) (Fin n) ℂ), InfKA.entryCLM a b M = M a b :=
    fun _ _ _ => rfl
  simp only [Ssum, InfKA.Ek, smul_add, Finset.sum_add_distrib, smul_smul, hφ]
  set A' := toMK k⁻¹ * A * toMK k with hA'
  have hl : ∀ a b, (A' * Matrix.single a b (1 : ℂ) - Matrix.single a b (1 : ℂ) * A') a b =
      A' a a - A' b b := by
    intro a b
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
  congr 1
  · rw [lowMinusUp_expand hB, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul]
  · simp only [← Finset.sum_smul]
    congr 1
    simp only [hl, Finset.sum_filter]
    have hsplit : ∀ a b : Fin n,
        (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * (A' a a - A' b b) else 0) =
          (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * A' a a else 0) +
          (if ε a = ε b ∧ a ≠ b then (if a < b then (1 : ℂ) else -1) * A' b b else 0) := by
      intro a b
      by_cases h : ε b = ε a ∧ b ≠ a
      · have h' : ε a = ε b ∧ a ≠ b := ⟨h.1.symm, Ne.symm h.2⟩
        rw [if_pos h, if_pos h, if_pos h']
        rcases lt_or_gt_of_ne h.2 with hab | hab
        · simp only [if_pos hab, if_neg (not_lt.2 hab.le)]
          ring
        · simp only [if_pos hab, if_neg (not_lt.2 hab.le)]
          ring
      · have h' : ¬ (ε a = ε b ∧ a ≠ b) := fun h' => h ⟨h'.1.symm, Ne.symm h'.2⟩
        rw [if_neg h, if_neg h, if_neg h', add_zero]
    simp only [hsplit, Finset.sum_add_distrib]
    conv_lhs => arg 2; rw [Finset.sum_comm]
    rw [← two_mul]
    have hc : ∀ a, ∑ b, (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * A' a a else 0) =
        -2 * ((rhoC ε a : ℝ) : ℂ) * A' a a := by
      intro a
      have hp : ∀ b, (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * A' a a else 0) =
          ((if b < a ∧ ε b = ε a then (1 : ℂ) else 0) - (if a < b ∧ ε b = ε a then (1 : ℂ) else 0)) *
            A' a a := by
        intro b
        rcases lt_trichotomy b a with h | rfl | h
        · by_cases he : ε b = ε a <;> simp [h, he, ne_of_lt h, not_lt.2 h.le]
        · simp
        · by_cases he : ε b = ε a <;> simp [h, he, ne_of_gt h, not_lt.2 h.le]
      simp only [hp]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
      delta rhoC
      push_cast
      ring
    simp only [hc]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

lemma pt (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsBlock ε A) (hAh : Aᴴ = A) (k : KG ε) :
    fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k) (toMK k⁻¹ * (A * x + x * A) * toMK k) •
        (T.op k * projW T * T.op k⁻¹) =
      Ssum T μ x A k - (T.dτ A * Gint T μ x k + Gint T μ x k * T.dτ A) := by
  have hmk : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun _ _ => rfl
  have hop : ∀ a b : KG ε, T.op (a * b) = T.op a * T.op b := fun a b => by simp [KType.op, map_mul]
  have hop1 : T.op 1 = 1 := by simp [KType.op]
  have hkk : toMK k * toMK k⁻¹ = 1 := by rw [← hmk, mul_inv_cancel]; rfl
  have hok : T.op k * T.op k⁻¹ = 1 := by rw [← hop, mul_inv_cancel, hop1]
  have hok' : T.op k⁻¹ * T.op k = 1 := by rw [← hop, inv_mul_cancel, hop1]
  have hAJ : A * Jm ε = Jm ε * A := (kfa_comm_iff_block ε A).mpr hA
  have hk1 : toMK k * Jm ε = Jm ε * toMK k := (show toMK k ∈ Kset ε from k.2).2
  have hk2 : toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹ := (show toMK k⁻¹ ∈ Kset ε from (k⁻¹).2).2
  have hH : toMK k⁻¹ * (A * x + x * A) * toMK k =
      (toMK k⁻¹ * A * toMK k) * (toMK k⁻¹ * x * toMK k) + (toMK k⁻¹ * x * toMK k) * (toMK k⁻¹ * A * toMK k) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (toMK k) (toMK k⁻¹), hkk, Matrix.one_mul]
  have hBJ : (toMK k⁻¹ * A * toMK k) * Jm ε = Jm ε * (toMK k⁻¹ * A * toMK k) := by
    calc toMK k⁻¹ * A * toMK k * Jm ε = toMK k⁻¹ * (A * (toMK k * Jm ε)) := by simp only [Matrix.mul_assoc]
      _ = toMK k⁻¹ * (A * Jm ε) * toMK k := by rw [hk1]; simp only [Matrix.mul_assoc]
      _ = toMK k⁻¹ * Jm ε * (A * toMK k) := by rw [hAJ]; simp only [Matrix.mul_assoc]
      _ = Jm ε * (toMK k⁻¹ * A * toMK k) := by rw [hk2]; simp only [Matrix.mul_assoc]
  have hBb : IsBlock ε (toMK k⁻¹ * A * toMK k) := (kfa_comm_iff_block ε _).mp hBJ
  have hBh : (toMK k⁻¹ * A * toMK k)ᴴ = toMK k⁻¹ * A * toMK k := by
    rw [InfKA.toMK_inv_eq]; simp [Matrix.conjTranspose_mul, hAh, Matrix.mul_assoc]
  have hdB : T.dτ (toMK k⁻¹ * A * toMK k) = T.op k⁻¹ * T.dτ A * T.op k := by
    have h := dtau_conj T k⁻¹ hA
    rw [inv_inv] at h
    exact h.symm
  have hk3 : ∀ X, T.op k * (T.op k⁻¹ * X) = X := fun X => by rw [← mul_assoc, hok, one_mul]
  have hdA : T.dτ A * (T.op k * projW T * T.op k⁻¹) + (T.op k * projW T * T.op k⁻¹) * T.dτ A =
      T.op k * (T.dτ (toMK k⁻¹ * A * toMK k) * projW T + projW T * T.dτ (toMK k⁻¹ * A * toMK k)) *
        T.op k⁻¹ := by
    rw [hdB]
    simp only [mul_assoc, mul_add, add_mul, hk3, hok, mul_one]
  have hconj : T.dτ A * Gint T μ x k + Gint T μ x k * T.dτ A =
      PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * (T.dτ (lowMinusUp (toMK k⁻¹ * A * toMK k)) * projW T -
          projW T * T.dτ (lowMinusUp (toMK k⁻¹ * A * toMK k))) * T.op k⁻¹) +
        ((2 * ∑ a, ((lowK ε lam a : ℝ) : ℂ) * (toMK k⁻¹ * A * toMK k) a a) * PhiM μ (toMK k⁻¹ * x * toMK k)) •
          (T.op k * projW T * T.op k⁻¹) := by
    simp only [Gint]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, hdA, tau_part T hBb hBh]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    module
  rw [hH, phiM_part μ (InfKA.conj_mem_omega hx k), Ssum_eq T μ x A k hBb, InfKA.DkL_apply, hconj, scal (ε := ε) μ hμ]
  simp only [Gint]
  module

end InfKH

theorem psM_inf_herm (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsBlock ε A) (hAh : Aᴴ = A) :
    fderiv ℂ (psM T μ) x (A * x + x * A) = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) := by
  have := compactSpace_KG ε
  obtain ⟨U, -, hPU, -, -, hder⟩ := psM_holo T μ
  rw [hder x (hPU hx)]
  have hGI : Integrable (Gint T μ x) (muK ε) := InfKA.integrable_of_cont (InfKA.continuous_Gint T μ hx)
  have hL : ∫ k, T.dτ A * Gint T μ x k ∂(muK ε) = T.dτ A * ∫ k, Gint T μ x k ∂(muK ε) :=
    (ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.dτ A)).integral_comp_comm hGI
  have hR : ∫ k, Gint T μ x k * T.dτ A ∂(muK ε) = (∫ k, Gint T μ x k ∂(muK ε)) * T.dτ A :=
    ((ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V)).flip (T.dτ A)).integral_comp_comm hGI
  have hLI : Integrable (fun k => T.dτ A * Gint T μ x k) (muK ε) :=
    (ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.dτ A)).integrable_comp hGI
  have hRI : Integrable (fun k => Gint T μ x k * T.dτ A) (muK ε) :=
    ((ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V)).flip (T.dτ A)).integrable_comp hGI
  obtain ⟨hSI, hS0⟩ := InfKH.integral_Ssum T μ hx A
  have hLR : Integrable (fun k => T.dτ A * Gint T μ x k + Gint T μ x k * T.dτ A) (muK ε) := hLI.add hRI
  rw [integral_congr_ae (Filter.Eventually.of_forall (InfKH.pt T μ hμ hx hA hAh)),
    integral_sub hSI hLR, hS0, zero_sub, integral_add hLI hRI, hL, hR]
  have hps : psM T μ x = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
      ∫ k, Gint T μ x k ∂(muK ε) := rfl
  rw [hps]
  simp only [smul_neg, smul_add, mul_smul_comm, smul_mul_assoc]

end ReciprocityTheory.ChartRestriction.DS.S7

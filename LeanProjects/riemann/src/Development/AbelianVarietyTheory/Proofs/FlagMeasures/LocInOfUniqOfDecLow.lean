import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOneOfUniq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OpnFrobCompare

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalInputs

theorem hpk_det (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem urep_of_ds {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : IsDSHpk k r ε lam σ) : IsURepOn (GG k r) σ := by
  obtain ⟨P, ⟨⟨hP, hH⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, -⟩ := h
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hiP : P⁻¹ * P = 1 := nonsing_inv_mul _ hd
  have mem : ∀ g, g ∈ GG k r ↔ P * g * P⁻¹ ∈ UJset ε := uHConj _ ε _ P hd hH
  have back : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hiP]; simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [hiP] using h1
  · intro a ha b hb
    have := hm _ ((mem a).1 ha) _ ((mem b).1 hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hiP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    simpa only [e, back] using this
  · intro g hg v
    have := hn _ ((mem g).1 hg) v
    simpa only [back] using this
  · intro v
    have hcont : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp hcont.continuousOn (s := GG k r) (fun g hg => (mem g).1 hg)
    refine this.congr fun g _ => ?_
    simp only [Function.comp, back]

theorem opn_pos {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := by
  have hu := ((uHGroup _ _ (hpk_det k r)).2.2 g hg).1
  have h := opn_mul_le g⁻¹ g
  rw [nonsing_inv_mul _ hu, opn_one] at h
  rcases (opn_nonneg g).lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0] at h; linarith

theorem coef_translate {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {a b g : Mat k r} (ha : a ∈ GG k r)
    (hb : b ∈ GG k r) (hg : g ∈ GG k r) (u v : H) :
    coef σ (σ a u) (σ b v) g = coef σ u v (b⁻¹ * g * a) := by
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ (hpk_det k r)
  have hx : b⁻¹ * g * a ∈ GG k r := hmul _ (hmul _ (hinv b hb).2 _ hg) _ ha
  have e : g * a = b * (b⁻¹ * g * a) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (hinv b hb).1, Matrix.one_mul]
  have e2 : σ g (σ a u) = σ b (σ (b⁻¹ * g * a) u) := by
    have h1 := hσ.1.2 g hg a ha
    have h2 := hσ.1.2 b hb _ hx
    rw [← e, h1] at h2
    exact congrArg (fun T : H →L[ℂ] H => T u) h2
  unfold coef
  rw [e2]
  exact (LinearIsometry.mk (σ b : H →ₗ[ℂ] H) (hσ.2.1 b hb)).inner_map_map v _

theorem decay_span {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {V : Set H} {a : ℝ} (ha : 0 ≤ a) (hσ : IsURepOn (GG k r) σ) (hV : Decay σ V a) :
    Decay σ (Submodule.span ℂ {v | ∃ g ∈ GG k r, ∃ u ∈ V, v = σ g u} : Submodule ℂ H) a := by
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ (hpk_det k r)
  intro u hu v hv
  refine Submodule.span_induction₂ (p := fun u v _ _ => ∃ C : ℝ, ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  · rintro _ _ ⟨x, hx, u, hu, rfl⟩ ⟨y, hy, v, hv, rfl⟩
    obtain ⟨C, hC⟩ := hV u hu v hv
    have hK : 0 < opn y * opn x⁻¹ := mul_pos (opn_pos hy) (opn_pos (hinv x hx).2)
    refine ⟨|C| * (opn y * opn x⁻¹) ^ a, fun g hg => ?_⟩
    have hm : y⁻¹ * g * x ∈ GG k r := hmul _ (hmul _ (hinv y hy).2 _ hg) _ hx
    rw [coef_translate hσ hx hy hg]
    have e : g = y * (y⁻¹ * g * x) * x⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (hinv y hy).1, Matrix.one_mul,
        Matrix.mul_assoc, mul_nonsing_inv _ (hinv x hx).1, Matrix.mul_one]
    have h1 : opn g ≤ opn y * opn x⁻¹ * opn (y⁻¹ * g * x) := by
      calc opn g = opn (y * (y⁻¹ * g * x) * x⁻¹) := by rw [← e]
        _ ≤ opn (y * (y⁻¹ * g * x)) * opn x⁻¹ := opn_mul_le _ _
        _ ≤ opn y * opn (y⁻¹ * g * x) * opn x⁻¹ :=
          mul_le_mul_of_nonneg_right (opn_mul_le _ _) (opn_nonneg _)
        _ = _ := by ring
    have h2 := Real.rpow_le_rpow_of_nonpos (opn_pos hg) h1 (neg_nonpos.2 ha)
    rw [Real.mul_rpow hK.le (opn_nonneg _)] at h2
    have hp := opn_pos hm
    calc _ ≤ |C| * opn (y⁻¹ * g * x) ^ (-a) :=
          (hC _ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      _ = |C| * (opn y * opn x⁻¹) ^ a * ((opn y * opn x⁻¹) ^ (-a) * opn (y⁻¹ * g * x) ^ (-a)) := by
          rw [mul_assoc |C|, ← mul_assoc (_ ^ a), ← Real.rpow_add hK]; simp
      _ ≤ _ := by gcongr
  · exact fun y _ => ⟨0, fun g _ => by simp [coef]⟩
  · exact fun y _ => ⟨0, fun g _ => by simp [coef]⟩
  · rintro x y z - - - ⟨C, hC⟩ ⟨C', hC'⟩
    refine ⟨C + C', fun g hg => ?_⟩
    rw [coef_add_left, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC g hg) (hC' g hg))
  · rintro x y z - - - ⟨C, hC⟩ ⟨C', hC'⟩
    refine ⟨C + C', fun g hg => ?_⟩
    rw [coef_add_right, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC g hg) (hC' g hg))
  · rintro c x y - - ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [coef_smul_left, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)
  · rintro c x y - - ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [coef_smul_right, norm_mul, norm_star, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)

theorem gap_of_nodes (D : D7) (τ : D.what₂.Tau) (h : ℝ) (hanti : StrictAnti (lamD D τ))
    (hb : ∀ j, 1 ≤ j → j + 1 ≤ D.R.m → h ≤ bOne D τ (j + 1) - bOne D τ j) :
    GapAtLeast (epsSH D.R) (lamD D τ) h := by
  have hd := dimS_eq D.R
  have hm := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have step : ∀ (i : ℕ) (hi : i + 1 < 2 * D.R.rS + D.R.k + 1), D.R.k - 1 ≤ i →
      h ≤ lamD D τ ⟨i, by omega⟩ - lamD D τ ⟨i + 1, hi⟩ := by
    intro i hi hk
    have h0 := hb (i - (D.R.k - 1) + 1) (by omega) (by omega)
    unfold bOne at h0
    rw [dif_pos (by omega), dif_pos (by omega)] at h0
    unfold lamD lamSH lamS
    simp only [Fin.val_cast]
    rw [dif_neg (by omega), dif_pos (by omega), dif_neg (by omega), dif_pos (by omega)]
    have e : i + 1 - (D.R.k - 1) = i - (D.R.k - 1) + 1 := by omega
    simp only [e, Nat.add_sub_cancel] at h0 ⊢
    linarith
  have key : ∀ a b : Fin (2 * D.R.rS + D.R.k + 1), a < b → epsSH D.R a ≠ epsSH D.R b →
      h ≤ lamD D τ a - lamD D τ b := by
    intro a b hab hne
    have hab' : a.val < b.val := hab
    have hb' := b.isLt
    by_cases ha : D.R.k - 1 ≤ a.val
    · have h1 := step a.val (by omega) ha
      have h2 := hanti.antitone (show (⟨a.val + 1, by omega⟩ : Fin _) ≤ b from hab')
      simp only [Fin.eta] at h1
      linarith
    · have hbk : D.R.k ≤ b.val := by
        by_contra hc
        apply hne
        unfold epsSH epsS
        simp only [Fin.val_cast]
        rw [if_pos (by omega)]
        split_ifs
        · rfl
        · have : b.val - (D.R.k - 1) = 0 := by omega
          simp [this]
      have h1 := step (b.val - 1) (by omega) (by omega)
      have h2 := hanti.antitone (show a ≤ (⟨b.val - 1, by omega⟩ : Fin _) from by
        show a.val ≤ b.val - 1; omega)
      have e : (⟨b.val - 1 + 1, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) = b := Fin.ext (by simp only; omega)
      rw [e] at h1
      linarith
  intro a b hne
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact (key a b h1 hne).trans (le_abs_self _)
  · exact absurd (by rw [h1]) hne
  · rw [abs_sub_comm]; exact (key b a h1 hne.symm).trans (le_abs_self _)

theorem decay_low (hD : Formalism.FourierDecayAlt.ThreeDimData.DecLow) {k r : ℕ} (hk : 1 ≤ k) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (hl : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hg : GapAtLeast ε lam (((2 * r + k + 1 : ℕ) : ℝ) ^ 19))
    {P : Mat k r} (hP : IsCayleyU k r ε P) :
    Decay σ (lowKSub ε lam (fun g => σ (P⁻¹ * g * P))) (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5) := by
  intro u hu v hv
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hr : 2 * ((r : ℝ) + 1) ≤ n := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [hn]; push_cast; linarith
  have hn2 : 2 ≤ n := by have : (0 : ℝ) ≤ r := by positivity
                         linarith
  have h13 : (120 : ℝ) ≤ n ^ 13 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn2 13)
  have h16 : (120 : ℝ) ≤ n ^ 16 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn2 16)
  have hh : 120 * n ^ 3 ≤ n ^ 19 := by
    have : n ^ 19 = n ^ 16 * n ^ 3 := by ring
    rw [this]; gcongr
  obtain ⟨C, hC⟩ := hD k r hk ε lam (n ^ 19) H σ hl hσ hg hh P hP u v hu hv
  have hs : Real.sqrt (2 * ((r : ℝ) + 1)) ≤ n := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hs0 : 0 < Real.sqrt (2 * ((r : ℝ) + 1)) := by positivity
  have he : 2 * n ^ 5 ≤ n ^ 19 / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) := by
    rw [le_div_iff₀ (by positivity)]
    calc 2 * n ^ 5 * (8 * Real.sqrt (2 * ((r : ℝ) + 1))) ≤ 2 * n ^ 5 * (8 * n) := by gcongr
      _ = 16 * n ^ 6 := by ring
      _ ≤ n ^ 13 * n ^ 6 := by gcongr; linarith
      _ = _ := by ring
  obtain ⟨K, hK, hc⟩ := GlobalTheory.SOrb.CCBridge.opn_gN_compare k r
  refine ⟨|C| * K ^ |-(2 * n ^ 5)|, fun g hg => ?_⟩
  have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have h2 : Formalism.FourierDecayAlt.B.gN g ^ (-(2 * n ^ 5)) ≤ K ^ |-(2 * n ^ 5)| * opn g ^ (-(2 * n ^ 5)) :=
    GlobalTheory.SOrb.CCBridge.rpow_compare hK _ (by linarith) (opn_pos hg) (hc g).2 (hc g).1
  calc _ ≤ |C| * Formalism.FourierDecayAlt.B.gN g ^ (-(n ^ 19 / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))) :=
        (hC g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    _ ≤ |C| * Formalism.FourierDecayAlt.B.gN g ^ (-(2 * n ^ 5)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (abs_nonneg _)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

end GlobalTheory.Amp.LocalInputs

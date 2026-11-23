import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProductStatement

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

namespace GlobalTheory.Mem

def PosDirichlet (F : ℂ → ℂ) : Prop :=
  ∃ (ι : Type) (w : ι → ℝ) (N : ι → ℕ), (∀ i, 0 ≤ w i) ∧ (∀ i, N i ≠ 0) ∧
    ∀ s : ℂ, 1 < s.re → HasSum (fun i => (w i : ℂ) * (N i : ℂ) ^ (-s)) (F s)

namespace PosDirichlet

lemma congr {F G : ℂ → ℂ} (h : PosDirichlet F) (e : ∀ s : ℂ, 1 < s.re → F s = G s) :
    PosDirichlet G := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := h
  exact ⟨ι, w, N, hw, hN, fun s hs => e s hs ▸ h s hs⟩

lemma const {c : ℝ} (hc : 0 ≤ c) : PosDirichlet (fun _ => (c : ℂ)) :=
  ⟨Unit, fun _ => c, fun _ => 1, fun _ => hc, fun _ => one_ne_zero, fun s _ => by
    simpa using hasSum_unique (fun _ : Unit => (c : ℂ))⟩

lemma hasSum_mul_of_norm_summable {ι κ : Type} {f : ι → ℂ} {g : κ → ℂ} {a b : ℂ} (hf : HasSum f a)
    (hg : HasSum g b) : HasSum (fun p : ι × κ => f p.1 * g p.2) (a * b) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

lemma mul {F G : ℂ → ℂ} (hF : PosDirichlet F) (hG : PosDirichlet G) :
    PosDirichlet (fun s => F s * G s) := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := hF
  obtain ⟨κ, w', N', hw', hN', h'⟩ := hG
  refine ⟨ι × κ, fun p => w p.1 * w' p.2, fun p => N p.1 * N' p.2,
    fun p => mul_nonneg (hw _) (hw' _), fun p => mul_ne_zero (hN _) (hN' _), fun s hs => ?_⟩
  have e : ∀ p : ι × κ, ((w p.1 * w' p.2 : ℝ) : ℂ) * ((N p.1 * N' p.2 : ℕ) : ℂ) ^ (-s) =
      ((w p.1 : ℂ) * (N p.1 : ℂ) ^ (-s)) * ((w' p.2 : ℂ) * (N' p.2 : ℂ) ^ (-s)) := by
    intro p
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  have h1 := hasSum_mul_of_norm_summable (h s hs) (h' s hs)
  beta_reduce at h1 ⊢
  rw [funext e]
  exact h1

lemma pow {F : ℂ → ℂ} (hF : PosDirichlet F) (j : ℕ) : PosDirichlet (fun s => F s ^ j) := by
  induction j with
  | zero => simpa using const zero_le_one
  | succ j ih => simpa only [pow_succ] using ih.mul hF

lemma norm_term {w : ℝ} (hw : 0 ≤ w) {N : ℕ} (hN : N ≠ 0) (s : ℂ) :
    ‖(w : ℂ) * (N : ℂ) ^ (-s)‖ = ((w : ℂ) * (N : ℂ) ^ (-(s.re : ℂ))).re := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN), Complex.norm_real,
    Real.norm_of_nonneg hw, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg N), ← Complex.ofReal_mul, Complex.ofReal_re, neg_re]

lemma tsum {J : Type} {F : J → ℂ → ℂ} (hF : ∀ j, PosDirichlet (F j))
    (hs : ∀ s : ℂ, 1 < s.re → Summable (fun j => F j s)) :
    PosDirichlet (fun s => ∑' j, F j s) := by
  choose ι w N hw hN h using hF
  refine ⟨Σ j, ι j, fun p => w p.1 p.2, fun p => N p.1 p.2, fun p => hw _ _, fun p => hN _ _,
    fun s hs' => ?_⟩
  have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs'
  have key : ∀ j, HasSum (fun i => ‖(w j i : ℂ) * (N j i : ℂ) ^ (-s)‖) (F j s.re).re := by
    intro j
    simp only [norm_term (hw _ _) (hN _ _)]
    exact Complex.hasSum_re (h j _ hσ)
  have hsum : Summable (fun p : Σ j, ι j => (w p.1 p.2 : ℂ) * (N p.1 p.2 : ℂ) ^ (-s)) := by
    apply Summable.of_norm
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun j => (key j).summable, ?_⟩
    simp only [fun j => (key j).tsum_eq]
    exact (Complex.hasSum_re (hs _ hσ).hasSum).summable
  have h2 := hsum.hasSum.sigma (fun j => h j s hs')
  show HasSum _ (∑' j, F j s)
  rw [h2.tsum_eq]
  exact hsum.hasSum

lemma exists_LSeries {F : ℂ → ℂ} (hF : PosDirichlet F) :
    ∃ b : ℕ → ℂ, 0 ≤ b ∧ ∀ s : ℂ, 1 < s.re → LSeriesHasSum b s (F s) := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := hF
  refine ⟨fun n => ∑' i : N ⁻¹' {n}, (w i : ℂ), fun n => tsum_nonneg fun i =>
    Complex.zero_le_real.2 (hw i.1), fun s hs => ?_⟩
  have h1 := (h s hs).tsum_fiberwise N
  unfold LSeriesHasSum
  suffices e : ∀ n, LSeries.term (fun n => ∑' i : N ⁻¹' {n}, (w i : ℂ)) s n =
      ∑' i : N ⁻¹' {n}, (w i : ℂ) * (N i : ℂ) ^ (-s) by
    rw [funext e]; exact h1
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · haveI : IsEmpty (N ⁻¹' {0}) := ⟨fun i => hN i i.2⟩
    simp
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    have : N i = n := i.2
    rw [this]

lemma exp_sub_one {F : ℂ → ℂ} (hF : PosDirichlet F) :
    PosDirichlet (fun s => Complex.exp (F s) - 1) := by
  have h1 : ∀ z : ℂ, HasSum (fun j : ℕ => z ^ (j + 1) / ((j + 1).factorial : ℂ))
      (Complex.exp z - 1) := by
    intro z
    have := NormedSpace.expSeries_div_hasSum_exp z
    rw [← Complex.exp_eq_exp_ℂ, ← hasSum_nat_add_iff' 1] at this
    simpa using this
  refine (tsum (F := fun (j : ℕ) s => F s ^ (j + 1) / ((j + 1).factorial : ℂ)) (fun j => ?_)
    (fun s _ => (h1 _).summable)).congr fun s _ => (h1 _).tsum_eq
  refine ((hF.pow (j + 1)).mul (const (c := ((j + 1).factorial : ℝ)⁻¹) (by positivity))).congr
    fun s _ => ?_
  push_cast
  rw [div_eq_mul_inv]

lemma exists_LSeries_exp {F : ℂ → ℂ} (hF : PosDirichlet F) :
    ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧
      ∀ s : ℂ, 1 < s.re → LSeries b s = Complex.exp (F s) := by
  obtain ⟨b, hb, h⟩ := hF.exp_sub_one.exists_LSeries
  have hδ : (0 : ℕ → ℂ) ≤ LSeries.delta := fun n => by
    by_cases hn : n = 1 <;> simp [LSeries.delta, hn]
  have h2 : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (LSeries.delta + b) s (Complex.exp (F s)) := by
    intro s hs
    have h0 : LSeriesHasSum LSeries.delta s 1 := by
      unfold LSeriesHasSum
      have := hasSum_ite_eq (1 : ℕ) (1 : ℂ)
      convert this using 2 with n
      rw [LSeries.term_delta]
    simpa using h0.add (h s hs)
  refine ⟨LSeries.delta + b, add_nonneg hδ hb, ?_, ?_, fun s hs => (h2 s hs).LSeries_eq⟩
  · have : LSeries.delta 1 = 1 := by simp [LSeries.delta]
    rw [Pi.add_apply, this]
    exact add_pos_of_pos_of_nonneg one_pos (hb 1)
  · refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) fun y hy => ?_
    exact (h2 y (by simpa using hy)).LSeriesSummable

end PosDirichlet

lemma sum_characters_nonneg {G : Type} [CommGroup G] [Fintype (G →* ℂˣ)] (g : G) :
    0 ≤ ∑ χ : G →* ℂˣ, (χ g : ℂ) := by
  by_cases h : ∀ χ : G →* ℂˣ, χ g = 1
  · exact Finset.sum_nonneg fun χ _ => by simp [h χ]
  · push_neg at h
    obtain ⟨ψ, hψ⟩ := h
    have h1 : ∑ χ : G →* ℂˣ, (χ g : ℂ) = (ψ g : ℂ) * ∑ χ : G →* ℂˣ, (χ g : ℂ) := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft ψ)]
      simp
    have h2 : (1 - (ψ g : ℂ)) * ∑ χ : G →* ℂˣ, (χ g : ℂ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (Units.ext (sub_eq_zero.1 h3).symm) hψ
    · exact h3.ge

lemma norm_character {G : Type} [CommGroup G] [Fintype G] (χ : G →* ℂˣ) (g : G) :
    ‖(χ g : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G) _ Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

lemma natCast_pow_cpow_comm (q k : ℕ) (z : ℂ) : ((q : ℂ) ^ k) ^ z = ((q : ℂ) ^ z) ^ k := by
  rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

lemma posDirichlet_local {G : Type} [CommGroup G] [Fintype G] [Fintype (G →* ℂˣ)] (g : G)
    {q : ℕ} (hq : 2 ≤ q) :
    PosDirichlet (fun s => ∑ χ : G →* ℂˣ, -Complex.log (1 - (χ g : ℂ) * (q : ℂ) ^ (-s))) := by
  refine ⟨ℕ, fun k => (∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ)).re / k, fun k => q ^ k,
    fun k => div_nonneg (Complex.nonneg_iff.1 (sum_characters_nonneg _)).1 (Nat.cast_nonneg _),
    fun k => pow_ne_zero _ (by omega), fun s hs => ?_⟩
  have h1 : ∀ χ : G →* ℂˣ, ‖(χ g : ℂ) * (q : ℂ) ^ (-s)‖ < 1 := by
    intro χ
    rw [norm_mul, norm_character, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hq
    · simp only [neg_re]; linarith
  have h2 := hasSum_sum (s := Finset.univ)
    (fun χ _ => Complex.hasSum_taylorSeries_neg_log (h1 χ))
  convert h2 using 2 with k
  have h3 : (((∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ)).re : ℝ) : ℂ) = ∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ) :=
    (Complex.eq_re_of_ofReal_le (r := 0) (by simpa using sum_characters_nonneg (g ^ k))).symm
  rw [Complex.ofReal_div, h3, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Nat.cast_pow, natCast_pow_cpow_comm, mul_pow, map_pow, Units.val_pow_eq_pow_val]
  push_cast
  ring

theorem ray_prod_LSeries_nonneg : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) [Fintype (D.G →* ℂˣ)], ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧ ∀ s : ℂ, 1 < s.re → LSeries b s = ∏ χ : D.G →* ℂˣ, LSeries (D.coef χ) s := by
  intro K _ _ M hM D _
  have hsum : ∀ (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → Summable (fun v : D.Pr =>
      -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    intro χ s hs
    refine (Summable.clog_one_sub (Summable.of_norm ?_)).neg
    simpa only [norm_mul, norm_character, one_mul] using (GlobalTheory.T.ray_L_series_euler_product K M hM D χ s hs).2.1
  have hq : ∀ v : D.Pr, 2 ≤ Ideal.absNorm v.1.asIdeal := fun v =>
    NumberField.HeightOneSpectrum.one_lt_absNorm v.1
  obtain ⟨b, h0, h1, h2, h3⟩ := (PosDirichlet.tsum
    (fun v : D.Pr => posDirichlet_local (D.cls v.1.asIdeal) (hq v))
    (fun s hs => summable_sum fun χ _ => hsum χ s hs)).exists_LSeries_exp
  refine ⟨b, h0, h1, h2, fun s hs => ?_⟩
  rw [h3 s hs, Summable.tsum_finsetSum (fun χ _ => hsum χ s hs), Complex.exp_sum]
  exact Finset.prod_congr rfl fun χ _ => (GlobalTheory.T.ray_L_series_euler_product K M hM D χ s hs).2.2.symm

end GlobalTheory.Mem

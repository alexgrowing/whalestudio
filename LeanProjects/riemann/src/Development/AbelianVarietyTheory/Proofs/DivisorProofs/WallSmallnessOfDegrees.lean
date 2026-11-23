import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqDiscriminantMultipleStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4.NearWall

theorem abs_prod_le {α : Type} [Fintype α] (g : α → ℝ) (hg : ∀ x, |g x| ≤ 2) (x₀ : α) :
    |∏ x, g x| ≤ |g x₀| * 2 ^ Fintype.card α := by
  rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ x₀), abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [Finset.abs_prod]
  calc ∏ x ∈ Finset.univ.erase x₀, |g x| ≤ ∏ _x ∈ Finset.univ.erase x₀, (2 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun x _ => hg x)
    _ = 2 ^ (Finset.univ.erase x₀).card := by rw [Finset.prod_const]
    _ ≤ 2 ^ Fintype.card α := by
        apply pow_le_pow_right₀ (by norm_num)
        exact Finset.card_le_univ _

theorem abs_ev_delPol_le {ι : Type} [Fintype ι] {N : ℕ} (v : ι → Fin N → ℝ) (hv : ∀ τ i, |v τ i| ≤ 1)
    (τ₀ : ι) (a b : Fin N) (hab : a < b) :
    |ev v (delPol ι N)| ≤ |v τ₀ a - v τ₀ b| * 2 ^ Fintype.card (ι × Fin N × Fin N) := by
  have h := abs_prod_le (fun x : ι × Fin N × Fin N =>
    if x.2.1 < x.2.2 then v x.1 x.2.1 - v x.1 x.2.2 else 1) (by
      intro x
      split_ifs
      · have h1 := abs_le.mp (hv x.1 x.2.1)
        have h2 := abs_le.mp (hv x.1 x.2.2)
        rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      · norm_num) (τ₀, a, b)
  simp only [hab, if_true] at h
  convert h using 2
  simp only [ev, delPol, map_prod, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem anti_of_adj {N : ℕ} (v : Fin N → ℝ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → v b ≤ v a) (a b : Fin N)
    (hab : a ≤ b) : v b ≤ v a := by
  obtain ⟨b, hb⟩ := b
  have hab' : (a : ℕ) ≤ b := hab
  induction b, hab' using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have hn' : n < N := by omega
    exact (h ⟨n, hn'⟩ ⟨n + 1, hb⟩ rfl).trans (ih hn' hn)

variable {D : D7} (Y : ShimX D.what₂.Tau)

theorem abs_le_sup (u : Wt Y) (τ : D.what₂.Tau) (i : Fin Y.N) : |u τ i| ≤ supAbs Y u :=
  le_ciSup (f := fun x : Rt D.what₂.Tau Y.N => |u x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)

theorem sup_le (u : Wt Y) (c : ℝ) (hc : 0 ≤ c) (h : ∀ τ i, |u τ i| ≤ c) : supAbs Y u ≤ c :=
  Real.iSup_le (fun x => h x.1 x.2) hc

theorem offWall_gap (τ₀ : D.what₂.Tau) (t c₀ : ℝ) (u : Wt Y) (hu : u ∈ wallSet (N := Y.N) Y.j τ₀ c₀)
    (τ : D.what₂.Tau) (a b : Fin Y.N) (hab : (b : ℕ) = a + 1) :
    ((τ = τ₀ ∧ (b : ℕ) = Y.j) → offWall Y τ₀ t u τ a - offWall Y τ₀ t u τ b = 2 * t) ∧
    (¬ (τ = τ₀ ∧ (b : ℕ) = Y.j) → c₀ ≤ offWall Y τ₀ t u τ a - offWall Y τ₀ t u τ b) := by
  obtain ⟨_, h2, h3⟩ := hu
  constructor
  · rintro ⟨rfl, hb⟩
    have := h2 a b hab hb
    have ha : (a : ℕ) < Y.j := by omega
    have hb' : ¬ (b : ℕ) < Y.j := by omega
    simp [offWall, ha, hb', this]
  · intro hn
    have := h3 τ a b hab hn
    by_cases hτ : τ = τ₀
    · have hb : (b : ℕ) ≠ Y.j := fun h => hn ⟨hτ, h⟩
      by_cases ha : (a : ℕ) < Y.j
      · have hb' : (b : ℕ) < Y.j := by omega
        simp only [offWall, hτ, ha, hb', and_self, if_true]
        rw [hτ] at this; linarith
      · have hb' : ¬ (b : ℕ) < Y.j := by omega
        simp only [offWall, hτ, ha, hb', and_false, if_false]
        rw [hτ] at this; linarith
    · simp only [offWall, hτ, false_and, if_false]
      linarith

theorem offWall_abs (τ₀ : D.what₂.Tau) (t c₀ : ℝ) (ht : 0 ≤ t) (u : Wt Y)
    (hu : u ∈ wallSet (N := Y.N) Y.j τ₀ c₀) (τ : D.what₂.Tau) (i : Fin Y.N) :
    |offWall Y τ₀ t u τ i| ≤ 1 / 2 + 2 * t := by
  have h := abs_le.mp (hu.1 τ i)
  simp only [offWall]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [h.1, h.2]

theorem offWall_rat (τ₀ : D.what₂.Tau) (t : ℚ) (u : Wt Y) (hu : IsRat Y u) : IsRat Y (offWall Y τ₀ t u) := by
  intro τ i
  obtain ⟨q, hq⟩ := hu τ i
  simp only [offWall]
  split_ifs
  · exact ⟨q + 2 * t, by rw [hq]; push_cast; ring⟩
  · exact ⟨q, by rw [hq]; ring⟩

theorem squeeze_abs (d C L L' g G x : ℝ) (hd : 0 ≤ d) (hL : 0 ≤ L) (hL' : 0 ≤ L') (hLL : L' ≤ 3 * L)
    (hg : 0 ≤ g) (hG : g ≤ G) (h1 : d * (-(C * L')) * g ≤ x) (h2 : x ≤ d * (C * L) * g) :
    |x| ≤ d * (3 * |C| * L) * G := by
  have hC := abs_nonneg C
  have e1 : C * L' ≤ 3 * |C| * L := by
    have := mul_le_mul (le_abs_self C) hLL hL' hC
    linarith
  have e2 : C * L ≤ 3 * |C| * L := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C) hL
    have := mul_nonneg hC hL
    linarith
  have e0 : 0 ≤ d * (3 * |C| * L) := by positivity
  have e3 : d * (3 * |C| * L) * g ≤ d * (3 * |C| * L) * G := mul_le_mul_of_nonneg_left hG e0
  have e4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hd) hg
  have e5 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hd) hg
  rw [abs_le]; constructor <;> linarith

set_option maxHeartbeats 1000000 in

theorem wallSmall : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), 2 < D.R.f * (Y.N - 1) → Positive A → Squeeze A →
    Heights A → Degrees A → WallSmall A := by
  intro D Y A hf hP hS hH hD
  have hf1 : 1 ≤ D.R.f := by
    rcases Nat.eq_zero_or_pos D.R.f with h | h
    · rw [h] at hf; simp at hf
    · exact h
  have hf1' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hj := Y.j_lt
  have hj0 := Y.j_pos
  have hN : (0 : ℝ) < Y.N := by exact_mod_cast (by omega : 0 < Y.N)
  have hN1 : (1 : ℝ) ≤ Y.N := by exact_mod_cast (by omega : 1 ≤ Y.N)
  set c₀ : ℝ := 1 / (4 * (Y.N : ℝ)) with hc₀
  have hc0 : 0 < c₀ := by positivity
  have hc4 : c₀ ≤ 1 / 4 := by
    rw [hc₀]; apply one_div_le_one_div_of_le <;> linarith
  obtain ⟨s₁, hs₁, hP⟩ := hP 1
  obtain ⟨t₀, ht₀, C, hH⟩ := hH c₀ hc0
  obtain ⟨hw, -, hD, -⟩ := hD
  obtain ⟨s₂, hs₂, hD⟩ := hD 1
  obtain ⟨cf, hcf, hfl⟩ := GlobalTheory.T.flag_degree_eq_discriminant_multiple D.what₂.Tau Y.N
  set K : ℝ := supAbs Y A.dir + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ supAbs Y A.dir := Real.iSup_nonneg fun _ => abs_nonneg _
    linarith
  have hKd : ∀ τ i, |A.dir τ i| ≤ K := fun τ i => by linarith [abs_le_sup Y A.dir τ i]
  set δ : ℝ := min (min (min s₁ s₂) t₀) (min (c₀ / 2) (1 / (2 * K))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ s₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ ≤ s₂ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ3 : δ ≤ t₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ4 : δ ≤ c₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ5 : δ ≤ 1 / (2 * K) := (min_le_right _ _).trans (min_le_right _ _)
  set M : ℝ := 2 ^ Fintype.card (D.what₂.Tau × Fin Y.N × Fin Y.N) with hM
  refine ⟨∑ c, ((dimY Y : ℝ) + 1) * (3 * |C|) * (A.w c * (cf * (10 * D.R.f * M))),
    ⌈5 * (D.R.f : ℝ) / δ⌉₊ + 10, ?_⟩
  intro B hB τ₀ u hu hur t ht
  have hB10 : (10 : ℝ) ≤ B := by exact_mod_cast (by omega : 10 ≤ B)
  have hB0 : (0 : ℝ) < B := by linarith
  have hB2 : (2 : ℝ) ≤ B := by linarith
  have htR : (t : ℝ) = 5 * (D.R.f : ℝ) / B := by rw [ht]; push_cast; ring
  have htB : (t : ℝ) * B = 5 * D.R.f := by rw [htR]; field_simp
  have ht0 : (0 : ℝ) < t := by rw [htR]; positivity
  have htδ : (t : ℝ) ≤ δ := by
    have h1 : 5 * (D.R.f : ℝ) / δ ≤ B := by
      refine (Nat.le_ceil _).trans ?_
      exact_mod_cast (by omega : ⌈5 * (D.R.f : ℝ) / δ⌉₊ ≤ B)
    rw [div_le_iff₀ hδ0] at h1
    rw [htR, div_le_iff₀ hB0]; linarith
  have ht8 : (t : ℝ) ≤ 1 / 8 := by linarith
  have htK : (t : ℝ) * K ≤ 1 / 2 := by
    have := htδ.trans hδ5
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have ht2 : (t : ℝ) ^ 2 ≤ t := by nlinarith
  have ht2K : (t : ℝ) ^ 2 * K ≤ t / 2 := by nlinarith
  set v := offWall Y τ₀ t u with hv
  have hvr : IsRat Y v := offWall_rat Y τ₀ t u hur
  have hva : ∀ τ i, |v τ i| ≤ 3 / 4 := fun τ i => by
    have := offWall_abs Y τ₀ t c₀ ht0.le u hu τ i
    linarith
  have hvs : supAbs Y v ≤ 1 := sup_le Y v 1 zero_le_one fun τ i => by linarith [hva τ i]
  have hadj : ∀ τ (a b : Fin Y.N), (b : ℕ) = a + 1 → 2 * (t : ℝ) ≤ v τ a - v τ b := by
    intro τ a b hab
    have := offWall_gap Y τ₀ t c₀ u hu τ a b hab
    by_cases h : τ = τ₀ ∧ (b : ℕ) = Y.j
    · exact (this.1 h).ge
    · linarith [this.2 h]
  have hdirt : ∀ τ i, |(t : ℝ) ^ 2 * A.dir τ i| ≤ t / 2 := fun τ i => by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) ^ 2)]
    exact (mul_le_mul_of_nonneg_left (hKd τ i) (by positivity)).trans ht2K
  have hadj' : ∀ τ (a b : Fin Y.N), (b : ℕ) = a + 1 →
      (t : ℝ) ≤ A.sh v ((t : ℝ) ^ 2) τ a - A.sh v ((t : ℝ) ^ 2) τ b := by
    intro τ a b hab
    have h1 := hadj τ a b hab
    have h2 := abs_le.mp (hdirt τ a)
    have h3 := abs_le.mp (hdirt τ b)
    simp only [SlopeTestRemainingChoices.sh]
    linarith [h2.1, h2.2, h3.1, h3.2]
  have hdomv : Dominant Y v := fun τ a b hab =>
    anti_of_adj (v τ) (fun a b h => by linarith [hadj τ a b h]) a b hab
  have hdom : Dominant Y (A.sh v ((t : ℝ) ^ 2)) := fun τ a b hab =>
    anti_of_adj (A.sh v ((t : ℝ) ^ 2) τ) (fun a b h => by linarith [hadj' τ a b h]) a b hab
  have hjj : Y.j = Y.j - 1 + 1 := by omega
  have hgap : ∀ τ, (t : ℝ) ≤ gap Y v τ := fun τ => by
    have := hadj τ ⟨Y.j - 1, by omega⟩ ⟨Y.j, hj⟩ hjj
    simp only [gap]; linarith
  have hcpt : CptGaps Y c₀ v := fun τ a b hab hb =>
    (offWall_gap Y τ₀ t c₀ u hu τ a b hab).2 fun h => hb h.2
  have hnef : NefCond Y B (A.sh v ((t : ℝ) ^ 2)) := by
    intro τ
    have h1 : supAbs Y (A.sh v ((t : ℝ) ^ 2)) ≤ 1 := sup_le Y _ 1 zero_le_one fun τ i => by
      have h2 := abs_le.mp (hdirt τ i)
      have h3 := abs_le.mp (hva τ i)
      simp only [SlopeTestRemainingChoices.sh]
      rw [abs_le]; constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
    have h2 : (t : ℝ) ≤ gap Y (A.sh v ((t : ℝ) ^ 2)) τ := hadj' τ ⟨Y.j - 1, by omega⟩ ⟨Y.j, hj⟩ hjj
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ B - 2)
    have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * D.R.f)
    nlinarith
  refine ⟨hdom, ?_⟩
  have hs0 : (0 : ℚ) < t ^ 2 := by
    have : (0 : ℚ) < t := by exact_mod_cast ht0
    positivity
  have hcast : ((t ^ 2 : ℚ) : ℝ) = (t : ℝ) ^ 2 := by push_cast; ring
  obtain ⟨hsp, hnf⟩ := hP B hB2 v (t ^ 2) hvr hvs hs0 (by rw [hcast]; linarith) (by rw [hcast]; exact hdom)
    (by rw [hcast]; exact hnef)
  obtain ⟨hlo, hup⟩ := hH B hB2 v t hvr hvs (by exact_mod_cast ht0) (by linarith) hgap hcpt hnef
  have hdeg := hD B hB2 v (t ^ 2) hvr hvs hs0 (by rw [hcast]; linarith) hdomv (by rw [hcast]; exact hdom)
  have hL : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hL' : 0 ≤ Real.log (B / (t : ℝ) ^ 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; linarith
  have hLL : Real.log (B / (t : ℝ) ^ 2) ≤ 3 * Real.log B := by
    have : (3 : ℝ) * Real.log B = Real.log ((B : ℝ) ^ 3) := by rw [Real.log_pow]; norm_num
    rw [this]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have : (B : ℝ) ^ 3 * (t : ℝ) ^ 2 = B * ((t : ℝ) * B) ^ 2 := by ring
    rw [this, htB]
    have : (1 : ℝ) ≤ (5 * (D.R.f : ℝ)) ^ 2 := by nlinarith
    nlinarith
  have hflag : flagDeg D.what₂.Tau Y.N v ≤ cf * (10 * D.R.f * M) / B := by
    rw [hfl]
    have h1 := abs_ev_delPol_le v (fun τ i => by linarith [hva τ i]) τ₀ ⟨Y.j - 1, by omega⟩ ⟨Y.j, hj⟩
      (by rw [Fin.lt_def]; simp only; omega)
    rw [(offWall_gap Y τ₀ t c₀ u hu τ₀ ⟨Y.j - 1, by omega⟩ ⟨Y.j, hj⟩ hjj).1 ⟨rfl, rfl⟩,
      abs_of_pos (by linarith : (0 : ℝ) < 2 * (t : ℝ))] at h1
    have h2 : cf * (10 * D.R.f * M) / B = cf * (2 * t * M) := by rw [htR]; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) hcf.le
  rw [Y.arSelf_sum, Finset.sum_mul, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  have h1 := (hS _ hsp hnf c _).1 fun y _ => hlo y
  have h2 := (hS _ hsp hnf c _).2 (hup c)
  have h3 := squeeze_abs _ C _ _ _ (A.w c * (cf * (10 * D.R.f * M) / B)) _ (by positivity) hL hL' hLL (hdeg c).1
    ((hdeg c).2.trans (mul_le_mul_of_nonneg_left hflag (hw c).le)) h1 h2
  refine h3.trans (le_of_eq ?_)
  ring

end GlobalTheory.Mean4.NearWall

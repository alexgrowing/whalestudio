import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Restrict
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.UnitaryDecomposition PositivityTheory.RgHe

namespace BaseIntegrality

theorem two_mul_int {m : ℕ} {lam : Fin m → ℝ} (h : Formalism.QuantumDeterminants.IsHCParam lam) (a : Fin m) :
    ∃ z : ℤ, 2 * lam a = z := by
  obtain ⟨k, hk⟩ := h.2 a
  exact ⟨2 * k + (m : ℤ) - 1, by push_cast; linarith⟩

theorem diff_int {m : ℕ} {lam mu : Fin m → ℝ} (h : Formalism.QuantumDeterminants.IsHCParam lam) (h' : Formalism.QuantumDeterminants.IsHCParam mu) (a : Fin m) :
    ∃ z : ℤ, mu a - lam a = z := by
  obtain ⟨k, hk⟩ := h.2 a
  obtain ⟨k', hk'⟩ := h'.2 a
  exact ⟨k' - k, by push_cast; linarith⟩

theorem floor_eq {w : ℝ} {z : ℤ} (hw : w = z) (h0 : 0 ≤ w) : ((⌊w⌋₊ : ℕ) : ℝ) = w := by
  have hz : (0 : ℤ) ≤ z := by rw [hw] at h0; exact_mod_cast h0
  have e : w = ((z.toNat : ℕ) : ℝ) := by
    rw [hw]
    have := Int.toNat_of_nonneg hz
    exact_mod_cast this.symm
  rw [e, Nat.floor_natCast]

theorem one_le_of_int_lt {x y : ℝ} {zx zy : ℤ} (hx : x = zx) (hy : y = zy) (h : x < y) : 1 ≤ y - x := by
  rw [hx, hy] at h ⊢
  have h1 : zx < zy := by exact_mod_cast h
  have h2 : (zx : ℝ) + 1 ≤ zy := by exact_mod_cast h1
  linarith

theorem one_le_abs_sub {m : ℕ} {lam : Fin m → ℝ} (h : Formalism.QuantumDeterminants.IsHCParam lam) {a b : Fin m} (hab : a ≠ b) :
    1 ≤ |lam a - lam b| := by
  obtain ⟨ka, hka⟩ := h.2 a
  obtain ⟨kb, hkb⟩ := h.2 b
  have e : lam a - lam b = ((ka - kb : ℤ) : ℝ) := by push_cast; linarith
  have hne : ka - kb ≠ 0 := fun h0 => hab (h.1.injective (by rw [h0] at e; simpa [sub_eq_zero] using e))
  rw [e, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hne

theorem ds_ex {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (h : ℝ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : 8 * (m : ℝ) ^ 2 + 2 * m < h) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ := by
  refine ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap m ε lam hl h hg (Or.inr ?_)
  have hq : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ m :=
      (min_le_left _ _).trans (by unfold ReciprocityTheory.ChartRestriction.DS.pOf; exact (Finset.card_filter_le _ _).trans (by simp))
    exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 := mul_le_mul_of_nonneg_left hq hm0
  refine max_lt (by nlinarith) (by nlinarith)

end BaseIntegrality

theorem base_of_far_models_frame : Far → Models → Frame → Base := by
  intro hFar hMod hFr n ε lam ε' mu e hG hW
  have hl2 : ∀ i, ∃ z : ℤ, 2 * lam i = z := BaseIntegrality.two_mul_int hG.hc
  have hm2 : ∀ j, ∃ z : ℤ, 2 * mu j = z := BaseIntegrality.two_mul_int hG.hc'
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = ∑ i, |lam i| + ∑ j, |mu j| := ⟨_, rfl⟩
  have hs1 : 0 ≤ ∑ i, |lam i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hs2 : 0 ≤ ∑ j, |mu j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0 : 0 ≤ B := by rw [hBd]; linarith
  have hlB : ∀ i, |lam i| ≤ B := fun i => by
    have := Finset.single_le_sum (f := fun i => |lam i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hBd]; linarith
  have hmB : ∀ j, |mu j| ≤ B := fun j => by
    have := Finset.single_le_sum (f := fun j => |mu j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    rw [hBd]; linarith
  obtain ⟨K, hKB⟩ : ∃ K : ℕ, 2 * B + 1 ≤ (K : ℝ) := ⟨⌈2 * B + 1⌉₊, Nat.le_ceil _⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin (n + 1) → ℝ, d = fun i => 2 * lam i + K := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d' : Fin n → ℝ, d' = fun j => 2 * mu j + K := ⟨_, rfl⟩
  have hdi : ∀ i, d i = 2 * lam i + K := fun i => by rw [hd]
  have hdj : ∀ j, d' j = 2 * mu j + K := fun j => by rw [hd']
  have hv : ∀ x, Sum.elim d d' x = 2 * Sum.elim lam mu x + K := by
    rintro (x | x)
    · exact hdi x
    · exact hdj x
  have hne : ∀ a b, lam a ≠ mu b := fun a b h => by
    obtain ⟨x, hx⟩ := hG.hc.2 a
    obtain ⟨y, hy⟩ := hG.hc'.2 b
    have : ((2 * y : ℤ) : ℝ) = (2 * x + 1 : ℤ) := by push_cast at *; linarith
    have : 2 * y = 2 * x + 1 := by exact_mod_cast this
    omega
  have hinj : Function.Injective (Sum.elim lam mu) := by
    rintro (x | x) (y | y) h
    · exact congrArg _ (hG.hc.1.injective h)
    · exact absurd h (hne _ _)
    · exact absurd h.symm (hne _ _)
    · exact congrArg _ (hG.hc'.1.injective h)
  have hinjd : Function.Injective (Sum.elim d d') := fun x y h => hinj (by rw [hv, hv] at h; linarith)
  have hWd : HeWord ε d ε' d' := by
    intro x y h1 h2
    simp only [hv] at h1 h2
    refine hW x y (by linarith) fun z hz => h2 z ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hDint : ∀ x, ∃ z : ℤ, Sum.elim d d' x = z := by
    rintro (x | x)
    · obtain ⟨z, hz⟩ := hl2 x
      exact ⟨z + K, by simp only [Sum.elim_inl]; rw [hdi, hz]; push_cast; ring⟩
    · obtain ⟨z, hz⟩ := hm2 x
      exact ⟨z + K, by simp only [Sum.elim_inr]; rw [hdj, hz]; push_cast; ring⟩
  have hd'1 : ∀ a b, a < b → 1 ≤ d' a - d' b := fun a b hab => by
    have h1 := hG.hc'.1 hab
    obtain ⟨za, hza⟩ := hm2 a
    obtain ⟨zb, hzb⟩ := hm2 b
    have := BaseIntegrality.one_le_of_int_lt hzb hza (by linarith)
    rw [hdj, hdj]; linarith
  have hdpos : ∀ i, 1 ≤ d i := fun i => by
    rw [hdi]; have := abs_le.1 (hlB i); linarith
  have hd'pos : ∀ j, 1 ≤ d' j := fun j => by
    rw [hdj]; have := abs_le.1 (hmB j); linarith
  obtain ⟨g, hg, -⟩ := hFr n ε d ε' d' e hG.fits hinjd hWd
  obtain ⟨C, t₀, hFar'⟩ := hFar n ε ε' e lam d d' g hG.fits hg hd'1
  obtain ⟨M, hMge⟩ : ∃ M : ℕ, 2 * |C| + 2 * B + 100 * ((n : ℝ) + 1) ^ 3 + |t₀| + 1 ≤ (M : ℝ) :=
    ⟨_, Nat.le_ceil _⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = M := ⟨_, rfl⟩
  rw [← hmdef] at hMge
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hn3 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
  have hT0 : 0 ≤ |t₀| := abs_nonneg t₀
  have hm1 : 1 ≤ m := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ((M ^ 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  have htm : t = m ^ 2 := by rw [ht, hmdef]; push_cast; ring
  have ht0 : 0 ≤ t := by rw [htm]; positivity
  have hsq : Real.sqrt t = m := by rw [htm]; exact Real.sqrt_sq (by linarith)
  have htt0 : t₀ ≤ t := by
    have : m ≤ m ^ 2 := by nlinarith
    have := le_abs_self t₀
    rw [htm]; linarith
  have hhc : Formalism.QuantumDeterminants.IsHCParam (lam + t • d) := by
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · have h1 := hG.hc.1 hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdi]
      nlinarith [mul_nonneg ht0 (le_of_lt (sub_pos.2 h1))]
    · obtain ⟨k, hk⟩ := hG.hc.2 a
      obtain ⟨z, hz⟩ := hl2 a
      refine ⟨k + ((M ^ 2 : ℕ) : ℤ) * (z + K), ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hdi, hz, ht]
      push_cast at hk ⊢
      linear_combination hk
  have hgap2 : Formalism.QuantumDeterminants.GapAtLeast ε (lam + t • d) (200 * ((n : ℝ) + 1) ^ 3) := by
    intro a b hab
    have h1 := hG.gap a b hab
    have e1 : (lam + t • d) a - (lam + t • d) b = (lam a - lam b) * (1 + 2 * t) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdi]; ring
    rw [e1, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + 2 * t)]
    nlinarith [mul_nonneg (abs_nonneg (lam a - lam b)) ht0]
  have hgapL : GapAtLeast ε (lam + t • d) (200 * ((n : ℝ) + 1) ^ 3) := hgap2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨Hπ, i1, i2, π, hπ⟩ := BaseIntegrality.ds_ex ε (lam + t • d) hhc _ hgap2 (by push_cast; nlinarith)
  have : CompleteSpace Hπ := hπ.1
  obtain ⟨mu', hmc, hmb, hocc⟩ := hFar' t htt0 hhc hgapL Hπ π hπ
  have hmb' : ∀ j, |mu' j - t * d' j| ≤ |C| * m := fun j => by
    have := hmb j
    rw [hsq] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))
  have hgap' : Formalism.QuantumDeterminants.GapAtLeast ε' mu' (200 * ((n : ℝ) + 1) ^ 3) := by
    intro a b hab
    have hab' : a ≠ b := fun h => hab (by rw [h])
    obtain ⟨za, hza⟩ := hm2 a
    obtain ⟨zb, hzb⟩ := hm2 b
    have hd2 : 2 ≤ |d' a - d' b| := by
      have e0 : d' a - d' b = 2 * (mu a - mu b) := by rw [hdj, hdj]; ring
      rw [e0, abs_mul, abs_two]
      linarith [BaseIntegrality.one_le_abs_sub hG.hc' hab']
    have e1 := hmb' a
    have e2 := hmb' b
    have e3 : |t * (d' a - d' b)| ≤ |mu' a - mu' b| + |mu' a - t * d' a| + |mu' b - t * d' b| := by
      have : t * (d' a - d' b) = (mu' a - mu' b) - (mu' a - t * d' a) + (mu' b - t * d' b) := by ring
      rw [this]
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    rw [abs_mul, abs_of_nonneg ht0] at e3
    have e4 : 2 * t ≤ t * |d' a - d' b| := by nlinarith
    have e5 : m * (|C| + 100 * ((n : ℝ) + 1) ^ 3) ≤ m * m := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e6 : 100 * ((n : ℝ) + 1) ^ 3 ≤ m * (100 * ((n : ℝ) + 1) ^ 3) := le_mul_of_one_le_left (by positivity) hm1
    rw [htm] at e4
    nlinarith
  obtain ⟨Hσ, j1, j2, σ, hσ⟩ := BaseIntegrality.ds_ex ε' mu' hmc _ hgap' (by nlinarith)
  have : CompleteSpace Hσ := hσ.1
  obtain ⟨j, hj0, hj⟩ := hocc Hσ σ hσ
  have hGp : Gp ε (lam + t • d) ε' mu' e :=
    { fits := hG.fits, two := hG.two, neg := hG.neg, le := hG.le, hc := hhc, hc' := hmc, gap := hgap2, gap' := hgap' }
  have hOcc := (hMod n ε (lam + t • d) ε' mu' e hGp).1 ⟨Hπ, Hσ, i1, i2, j1, j2, π, σ, hπ, hσ, j, hj0, hj⟩
  obtain ⟨Wf, hWf⟩ : ∃ Wf : Fin (n + 1) ⊕ Fin n → ℝ, Wf = Sum.elim (fun i => t * d i) (fun j => mu' j - mu j) :=
    ⟨_, rfl⟩
  have hWint : ∀ x, ∃ z : ℤ, Wf x = z := by
    rintro (i | j)
    · obtain ⟨z, hz⟩ := hl2 i
      exact ⟨((M ^ 2 : ℕ) : ℤ) * (z + K), by rw [hWf]; simp only [Sum.elim_inl]; rw [hdi, hz, ht]; push_cast; ring⟩
    · obtain ⟨z, hz⟩ := BaseIntegrality.diff_int hG.hc' hmc j
      exact ⟨z, by rw [hWf]; simp only [Sum.elim_inr]; exact hz⟩
  have hr : ∀ x, |Wf x - t * Sum.elim d d' x| ≤ |C| * m + B := by
    rintro (i | j)
    · rw [hWf]; simp only [Sum.elim_inl, sub_self, abs_zero]; positivity
    · rw [hWf]; simp only [Sum.elim_inr]
      have h1 := hmb' j
      have h2 := hmB j
      have : mu' j - mu j - t * d' j = (mu' j - t * d' j) - mu j := by ring
      rw [this]
      exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hDge : ∀ x, t ≤ t * Sum.elim d d' x := by
    rintro (i | j)
    · simp only [Sum.elim_inl]; nlinarith [hdpos i]
    · simp only [Sum.elim_inr]; nlinarith [hd'pos j]
  have hm2' : m * (|C| + B + 1) ≤ m * m := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hBm : B ≤ B * m := le_mul_of_one_le_right hB0 hm1
  have hWnn : ∀ x, 0 ≤ Wf x := by
    intro x
    have h1 := hr x
    have h2 := hDge x
    have h3 := (abs_le.1 h1).1
    rw [htm] at h2
    nlinarith
  obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) ⊕ Fin n → ℕ, a = fun x => ⌊Wf x⌋₊ := ⟨_, rfl⟩
  have haW : ∀ x, (a x : ℝ) = Wf x := fun x => by
    obtain ⟨z, hz⟩ := hWint x
    rw [ha]
    exact BaseIntegrality.floor_eq hz (hWnn x)
  refine ⟨a, fun x y hxy => ?_, ?_⟩
  · rcases hxy.eq_or_lt with h | h
    · rw [hinj h]
    · have hlt : Sum.elim d d' x < Sum.elim d d' y := by rw [hv, hv]; linarith
      obtain ⟨zx, hzx⟩ := hDint x
      obtain ⟨zy, hzy⟩ := hDint y
      have h1 := BaseIntegrality.one_le_of_int_lt hzx hzy hlt
      have h2 := (abs_le.1 (hr x)).2
      have h3 := (abs_le.1 (hr y)).1
      have h4 : t ≤ t * Sum.elim d d' y - t * Sum.elim d d' x := by
        have := mul_le_mul_of_nonneg_left h1 ht0
        rw [mul_one, mul_sub] at this
        exact this
      have h5 : m * (2 * |C| + 2 * B + 1) ≤ m * m := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have e5 : m * (2 * |C| + 2 * B + 1) = 2 * (|C| * m) + 2 * (B * m) + m := by ring
      have hkey : 2 * (|C| * m) + 2 * B ≤ t := by
        rw [htm, sq]
        rw [e5] at h5
        linarith
      have hreal : (a x : ℝ) ≤ (a y : ℝ) := by
        rw [haW, haW]
        linarith
      exact Nat.cast_le.mp hreal
  · have e1 : (lam + fun i => (a (Sum.inl i) : ℝ)) = lam + t • d := funext fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [haW, hWf]
      simp only [Sum.elim_inl]
    have e2 : (mu + fun j => (a (Sum.inr j) : ℝ)) = mu' := funext fun j => by
      simp only [Pi.add_apply]
      rw [haW, hWf]
      simp only [Sum.elim_inr]
      ring
    rw [e1, e2]
    exact hOcc

end PositivityTheory.RgHe3

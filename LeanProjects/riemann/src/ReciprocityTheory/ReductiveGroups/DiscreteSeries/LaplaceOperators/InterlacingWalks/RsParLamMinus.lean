import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.AdjGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.Imports

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def rsExt {N : ℕ} (f : Fin N → ℝ) (x : ℕ) : ℝ := if h : x < N then f ⟨x, h⟩ else 0

theorem rsExt_mk {N : ℕ} (f : Fin N → ℝ) (x : ℕ) (h : x < N) : f ⟨x, h⟩ = rsExt f x := by
  rw [rsExt, dif_pos h]

def rsG (B : ℕ → ℝ) (t j m q : ℕ) : ℝ :=
  if q < j then -B q else if q = j then -B q - (j : ℝ) * t + m else -B q - (q : ℝ) * t

def rsF (k : ℕ) (U B : ℕ → ℝ) (t j m x : ℕ) : ℝ :=
  if x < k then U x - 1 / 2 else rsG B t j m (x - (k - 1))

def rsPt (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j m : ℕ) :
    Fin (2 * r + k + 1) → ℝ :=
  fun a => rsF k (rsExt u) (rsExt b) t j m a.val

theorem rsPt_zero (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j : ℕ) :
    rsPt k r u b t j 0 = raisePar k r u b t j := by
  funext a
  have ha := a.isLt
  simp only [rsPt, rsF, rsG, raisePar, rsExt]
  split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)

theorem rsPt_top (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j : ℕ) :
    rsPt k r u b t j (j * t) = raisePar k r u b t (j + 1) := by
  funext a
  have ha := a.isLt
  simp only [rsPt, rsF, rsG, raisePar, rsExt]
  split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)

theorem rsPt_succ (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j m : ℕ)
    (hk : 1 ≤ k) (hj : 1 ≤ j) (hj2 : j ≤ 2 * r + 1) :
    rsPt k r u b t j (m + 1) =
      rsPt k r u b t j m + Pi.single (⟨j + k - 1, by omega⟩ : Fin (2 * r + k + 1)) 1 := by
  funext a
  have ha := a.isLt
  simp only [Pi.add_apply, Pi.single_apply, rsPt, rsF, rsG, rsExt, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)

theorem rsG_step (B : ℕ → ℝ) (h : ℝ) (t j m q N : ℕ) (hm : m ≤ j * t)
    (hBlt : ∀ q, q + 1 < N → B q < B (q + 1)) (hBgap : ∀ q, q + 1 < N → h ≤ B (q + 1) - B q)
    (hq : q + 1 < N) :
    rsG B t j m (q + 1) < rsG B t j m q ∧ h ≤ rsG B t j m q - rsG B t j m (q + 1) := by
  have hBq := hBlt q hq
  have hgq := hBgap q hq
  have hmR : (m : ℝ) ≤ (j : ℝ) * t := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have e1 : ((q : ℝ) + 1) * t = (q : ℝ) * t + t := by ring
  unfold rsG
  rcases lt_trichotomy (q + 1) j with h1 | h1 | h1
  · rw [if_pos h1, if_pos (show q < j by omega)]
    constructor <;> linarith
  · rw [if_neg (show ¬ q + 1 < j by omega), if_pos h1, if_pos (show q < j by omega)]
    constructor <;> linarith
  · rcases Nat.lt_or_ge j q with h2 | h2
    · rw [if_neg (show ¬ q + 1 < j by omega), if_neg (show q + 1 ≠ j by omega),
        if_neg (show ¬ q < j by omega), if_neg (show q ≠ j by omega)]
      push_cast
      have hqt : (0 : ℝ) ≤ (q : ℝ) * t := by positivity
      constructor <;> linarith
    · have hqj : q = j := by omega
      have hqt : (q : ℝ) * t = (j : ℝ) * t := by rw [hqj]
      rw [if_neg (show ¬ q + 1 < j by omega), if_neg (show q + 1 ≠ j by omega),
        if_neg (show ¬ q < j by omega), if_pos hqj]
      push_cast
      constructor <;> linarith

theorem rsG_le (B : ℕ → ℝ) (t j m q : ℕ) (hm : m ≤ j * t) : rsG B t j m q ≤ -B q := by
  have hmR : (m : ℝ) ≤ (j : ℝ) * t := by exact_mod_cast hm
  have hqt : (0 : ℝ) ≤ (q : ℝ) * t := by positivity
  unfold rsG
  split_ifs <;> linarith

theorem rsG_int (B : ℕ → ℝ) (t j m q : ℕ) : ∃ z : ℤ, rsG B t j m q = -B q + z := by
  unfold rsG
  split_ifs
  · exact ⟨0, by simp⟩
  · exact ⟨(m : ℤ) - (j : ℤ) * (t : ℤ), by push_cast; ring⟩
  · exact ⟨-((q : ℤ) * (t : ℤ)), by push_cast; ring⟩

theorem rsF_step (k r : ℕ) (U B : ℕ → ℝ) (h : ℝ) (t j m x : ℕ) (hk : 1 ≤ k) (hm : m ≤ j * t)
    (hBlt : ∀ q, q + 1 < 2 * r + 2 → B q < B (q + 1))
    (hBgap : ∀ q, q + 1 < 2 * r + 2 → h ≤ B (q + 1) - B q)
    (hUlt : ∀ x, x + 1 < k → U (x + 1) < U x) (hUhalf : -B 0 ≤ U (k - 1) - 1 / 2)
    (hx : x + 1 < 2 * r + k + 1) :
    rsF k U B t j m (x + 1) < rsF k U B t j m x ∧
      (k - 1 ≤ x → h ≤ rsF k U B t j m x - rsF k U B t j m (x + 1)) := by
  by_cases hx1 : x + 1 < k
  · have hx0 : x < k := by omega
    rw [rsF, rsF, if_pos hx1, if_pos hx0]
    exact ⟨by linarith [hUlt x hx1], fun h' => absurd h' (by omega)⟩
  · by_cases hx0 : x < k
    · have hxk : x = k - 1 := by omega
      have e : x + 1 - (k - 1) = 1 := by omega
      rw [rsF, rsF, if_neg hx1, if_pos hx0, e]
      have hle := rsG_le B t j m 1 hm
      have hb01 : B 0 < B 1 := hBlt 0 (by omega)
      have hg01 : h ≤ B 1 - B 0 := hBgap 0 (by omega)
      have hU : U x = U (k - 1) := by rw [hxk]
      constructor
      · linarith
      · intro _
        linarith
    · have hq : x - (k - 1) + 1 < 2 * r + 2 := by omega
      have e : x + 1 - (k - 1) = x - (k - 1) + 1 := by omega
      rw [rsF, rsF, if_neg hx1, if_neg hx0, e]
      obtain ⟨h1, h2⟩ := rsG_step B h t j m (x - (k - 1)) (2 * r + 2) hm hBlt hBgap hq
      exact ⟨h1, fun _ => h2⟩

theorem rsParLam_minus (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (a : Fin (2 * r + k + 1)) (ha : k - 1 ≤ a.val) :
    parLam k r v b a = -rsExt b (a.val - (k - 1)) := by
  have h1 : ¬ a.val < k - 1 := by omega
  have h2 : a.val - (k - 1) < 2 * r + 2 := by have := a.isLt; omega
  simp only [parLam, rsExt, dif_neg h1, dif_pos h2]

theorem rsParEps_same (k r : ℕ) (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < 2 * r + k + 1)
    (hne : parEps k r a ≠ parEps k r ⟨a.val + 1, ha⟩) : k - 1 ≤ a.val := by
  by_contra hcon
  apply hne
  have e1 : parEps k r a = true := by
    show (if a.val < k - 1 then true else decide ((a.val - (k - 1)) % 2 = 0)) = true
    rw [if_pos (show a.val < k - 1 by omega)]
  have e2 : parEps k r ⟨a.val + 1, ha⟩ = true := by
    show (if a.val + 1 < k - 1 then true else decide ((a.val + 1 - (k - 1)) % 2 = 0)) = true
    split_ifs with h1
    · rfl
    · have : a.val + 1 - (k - 1) = 0 := by omega
      simp [this]
  rw [e1, e2]

private lemma strictAnti_lt_of_succ_lt (g : ℕ → ℝ) (n : ℕ) (hg : ∀ x, x + 1 < n → g (x + 1) < g x) :
    ∀ x y, x < y → y < n → g y < g x := by
  intro x y hxy hy
  induction y with
  | zero => omega
  | succ y ih =>
    rcases Nat.lt_or_ge x y with h1 | h1
    · exact lt_trans (hg y hy) (ih h1 (by omega))
    · have : x = y := by omega
      subst this
      exact hg x hy

private lemma gap_lemma_2 (g : ℕ → ℝ) (n c : ℕ) (h : ℝ)
    (hanti : ∀ x y, x < y → y < n → g y < g x)
    (hgap : ∀ x, x + 1 < n → c ≤ x → h ≤ g x - g (x + 1))
    (x y : ℕ) (hxy : x < y) (hy : y < n) (hc : c < y) : h ≤ g x - g y := by
  have h1 := hgap (y - 1) (by omega) (by omega)
  have e : y - 1 + 1 = y := by omega
  rw [e] at h1
  rcases Nat.lt_or_ge x (y - 1) with h2 | h2
  · have := hanti x (y - 1) h2 (by omega)
    linarith
  · have : x = y - 1 := by omega
    rw [this]
    exact h1

theorem raiseStep : RaiseStepStatement := by
  intro k r u v b h t P hk hpar hint hhalf hlow hSC j hj hj2 hP
  have hBlt : ∀ q, q + 1 < 2 * r + 2 → rsExt b q < rsExt b (q + 1) := by
    intro q hq
    have hq0 : q + (k - 1) < 2 * r + k + 1 := by omega
    have hq1 : q + (k - 1) + 1 < 2 * r + k + 1 := by omega
    have h1 := hpar.1 (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _) :
      (⟨q + (k - 1), hq0⟩ : Fin (2 * r + k + 1)) < ⟨q + (k - 1) + 1, hq1⟩)
    rw [rsParLam_minus k r v b ⟨q + (k - 1) + 1, hq1⟩ (show k - 1 ≤ q + (k - 1) + 1 by omega),
      rsParLam_minus k r v b ⟨q + (k - 1), hq0⟩ (show k - 1 ≤ q + (k - 1) by omega)] at h1
    have e1 : (⟨q + (k - 1), hq0⟩ : Fin (2 * r + k + 1)).val - (k - 1) = q := by
      show q + (k - 1) - (k - 1) = q
      omega
    have e2 : (⟨q + (k - 1) + 1, hq1⟩ : Fin (2 * r + k + 1)).val - (k - 1) = q + 1 := by
      show q + (k - 1) + 1 - (k - 1) = q + 1
      omega
    rw [e1, e2] at h1
    linarith
  have hBgap : ∀ q, q + 1 < 2 * r + 2 → h ≤ rsExt b (q + 1) - rsExt b q := by
    intro q hq
    rw [← rsExt_mk b (q + 1) hq, ← rsExt_mk b q (by omega)]
    exact hlow ⟨q, by omega⟩ hq
  have hUlt : ∀ x, x + 1 < k → rsExt u (x + 1) < rsExt u x := by
    intro x hx
    rw [← rsExt_mk u (x + 1) hx, ← rsExt_mk u x (by omega)]
    have h1 := hint.1 ⟨x, by omega⟩
    exact lt_trans h1.2 h1.1
  have hUhalf : -rsExt b 0 ≤ rsExt u (k - 1) - 1 / 2 := by
    have hk0 : k - 1 < k := by omega
    have h1 := hint.2 (by omega)
    obtain ⟨z, hz⟩ := hhalf ⟨k - 1, hk0⟩ ⟨k - 1, by omega⟩
    rw [rsParLam_minus k r v b ⟨k - 1, by omega⟩ (le_refl _)] at hz
    have e0 : rsExt b ((⟨k - 1, by omega⟩ : Fin (2 * r + k + 1)).val - (k - 1)) =
        b ⟨0, by omega⟩ := by
      show rsExt b (k - 1 - (k - 1)) = _
      rw [Nat.sub_self, ← rsExt_mk b 0 (by omega)]
    rw [e0] at hz
    rw [← rsExt_mk u (k - 1) hk0, ← rsExt_mk b 0 (by omega)]
    have hz0 : (-1 : ℤ) < z := by
      have : ((-1 : ℤ) : ℝ) < (z : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hz1 : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ z by omega)
    linarith
  have hstep : ∀ m, m ≤ j * t → ∀ x, x + 1 < 2 * r + k + 1 →
      rsF k (rsExt u) (rsExt b) t j m (x + 1) < rsF k (rsExt u) (rsExt b) t j m x ∧
      (k - 1 ≤ x → h ≤ rsF k (rsExt u) (rsExt b) t j m x - rsF k (rsExt u) (rsExt b) t j m (x + 1)) :=
    fun m hm x hx => rsF_step k r (rsExt u) (rsExt b) h t j m x hk hm hBlt hBgap hUlt hUhalf hx
  have hanti : ∀ m, m ≤ j * t → ∀ x y, x < y → y < 2 * r + k + 1 →
      rsF k (rsExt u) (rsExt b) t j m y < rsF k (rsExt u) (rsExt b) t j m x :=
    fun m hm => strictAnti_lt_of_succ_lt (fun z => rsF k (rsExt u) (rsExt b) t j m z) (2 * r + k + 1)
      (fun x hx => (hstep m hm x hx).1)
  have hepsc : ∀ x y : Fin (2 * r + k + 1), x.val < y.val → parEps k r x ≠ parEps k r y →
      k - 1 < y.val := by
    intro x y hxy hne
    by_contra hcon
    apply hne
    have e1 : parEps k r x = true := by
      show (if x.val < k - 1 then true else decide ((x.val - (k - 1)) % 2 = 0)) = true
      rw [if_pos (show x.val < k - 1 by omega)]
    have e2 : parEps k r y = true := by
      show (if y.val < k - 1 then true else decide ((y.val - (k - 1)) % 2 = 0)) = true
      split_ifs with h1
      · rfl
      · have : y.val - (k - 1) = 0 := by omega
        simp [this]
    rw [e1, e2]
  have hGap : ∀ m, m ≤ j * t → GapAtLeast (parEps k r) (rsPt k r u b t j m) h := by
    intro m hm x y hne
    have hg := gap_lemma_2 (fun z => rsF k (rsExt u) (rsExt b) t j m z) (2 * r + k + 1) (k - 1) h
      (hanti m hm) (fun z hz hc => (hstep m hm z hz).2 hc)
    rcases lt_trichotomy x.val y.val with h1 | h1 | h1
    · exact le_trans (hg x.val y.val h1 y.isLt (hepsc x y h1 hne)) (le_abs_self _)
    · exact absurd (congrArg (parEps k r) (Fin.ext h1)) hne
    · rw [abs_sub_comm]
      exact le_trans (hg y.val x.val h1 x.isLt (hepsc y x h1 (Ne.symm hne))) (le_abs_self _)
  have hHC : ∀ m, m ≤ j * t → IsHCPar (rsPt k r u b t j m) := by
    intro m hm
    refine ⟨fun x y hxy => hanti m hm x.val y.val hxy y.isLt, fun x => ?_⟩
    obtain ⟨z2, hz2⟩ := hpar.2 x
    by_cases hx : x.val < k
    · obtain ⟨z1, hz1⟩ := hhalf ⟨x.val, hx⟩ x
      refine ⟨z1 + z2, ?_⟩
      show rsF k (rsExt u) (rsExt b) t j m x.val - _ = _
      rw [rsF, if_pos hx, ← rsExt_mk u x.val hx, Int.cast_add]
      linarith
    · obtain ⟨z3, hz3⟩ := rsG_int (rsExt b) t j m (x.val - (k - 1))
      have hl := rsParLam_minus k r v b x (by omega)
      refine ⟨z3 + z2, ?_⟩
      show rsF k (rsExt u) (rsExt b) t j m x.val - _ = _
      rw [rsF, if_neg hx, hz3, Int.cast_add]
      linarith
  have key : ∀ m, m ≤ j * t → P (rsPt k r u b t j m) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [rsPt_zero]
      exact hP
    | succ m ih =>
      intro hm
      have hm' : m ≤ j * t := by omega
      rw [rsPt_succ k r u b t j m hk hj hj2]
      refine hSC.2 _ _ (hHC m hm') (hGap m hm') ?_ ?_ ?_ (ih hm')
      · rw [← rsPt_succ k r u b t j m hk hj hj2]
        exact hHC (m + 1) hm
      · rw [← rsPt_succ k r u b t j m hk hj hj2]
        exact hGap (m + 1) hm
      · intro i heq
        have hi : i.val < j + k - 1 := by have := i.isLt; omega
        have hlt := (hHC m hm').1 (Fin.mk_lt_mk.mpr hi :
          (⟨i.val, by omega⟩ : Fin (2 * r + k + 1)) < ⟨j + k - 1, by omega⟩)
        have hv : rsPt k r u b t j m ⟨i.val, by omega⟩ = u i - 1 / 2 := by
          show rsF k (rsExt u) (rsExt b) t j m i.val = u i - 1 / 2
          rw [rsF, if_pos i.isLt, ← rsExt_mk u i.val i.isLt]
        linarith
  have := key (j * t) le_rfl
  rwa [rsPt_top] at this

end ReciprocityTheory.ChartRestriction.DS.Lap

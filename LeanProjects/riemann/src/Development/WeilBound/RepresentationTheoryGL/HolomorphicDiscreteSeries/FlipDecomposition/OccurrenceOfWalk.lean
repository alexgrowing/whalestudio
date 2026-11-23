import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.FlipDecAlt

noncomputable section

open Finset

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

variable {n : ℕ}

def shL (lam : Fin (n + 1) → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) : Fin (n + 1) → ℝ := lam + fun i => (b (Sum.inl i) : ℝ)

def shM (mu : Fin n → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) : Fin n → ℝ := mu + fun j => (b (Sum.inr j) : ℝ)

theorem abs_le_shift {x y : ℝ} {p q : ℕ} (h1 : x ≤ y → p ≤ q) (h2 : y ≤ x → q ≤ p) :
    |x - y| ≤ |(x + p) - (y + q)| := by
  rcases le_total x y with h | h
  · have := h1 h
    have h' : (p : ℝ) ≤ q := by exact_mod_cast this
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have := h2 h
    have h' : (q : ℝ) ≤ p := by exact_mod_cast this
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

theorem hc_shift {m : ℕ} {lam : Fin m → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (c : Fin m → ℕ)
    (hc : ∀ i j, lam i ≤ lam j → c i ≤ c j) : Formalism.QuantumDeterminants.IsHCParam (lam + fun i => (c i : ℝ)) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h1 := hl.1 hij
    have h2 : (c j : ℝ) ≤ c i := by exact_mod_cast hc j i h1.le
    simp only [Pi.add_apply]
    linarith
  · obtain ⟨z, hz⟩ := hl.2 a
    exact ⟨z + c a, by simp only [Pi.add_apply]; push_cast; linarith⟩

theorem gap_shift {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (c : Fin m → ℕ)
    (hc : ∀ i j, lam i ≤ lam j → c i ≤ c j) : Formalism.QuantumDeterminants.GapAtLeast ε (lam + fun i => (c i : ℝ)) h := by
  intro a b hab
  refine (hg a b hab).trans ?_
  simp only [Pi.add_apply]
  exact abs_le_shift (hc a b) (hc b a)

def Mono (lam : Fin (n + 1) → ℝ) (mu : Fin n → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) : Prop :=
  ∀ x y, Sum.elim lam mu x ≤ Sum.elim lam mu y → b x ≤ b y

theorem gp_shift {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}
    {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hG : Gp ε lam ε' mu e) {b : Fin (n + 1) ⊕ Fin n → ℕ} (hb : Mono lam mu b) :
    Gp ε (shL lam b) ε' (shM mu b) e :=
  ⟨hG.fits, hG.two, hG.neg, hG.le, hc_shift hG.hc _ fun i j h => hb (Sum.inl i) (Sum.inl j) h,
    hc_shift hG.hc' _ fun i j h => hb (Sum.inr i) (Sum.inr j) h,
    gap_shift hG.gap _ fun i j h => hb (Sum.inl i) (Sum.inl j) h,
    gap_shift hG.gap' _ fun i j h => hb (Sum.inr i) (Sum.inr j) h⟩

theorem half {lam : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hm : Formalism.QuantumDeterminants.IsHCParam mu)
    (i : Fin (n + 1)) (j : Fin n) : ∃ z : ℤ, lam i - mu j = z + 1 / 2 := by
  obtain ⟨a, ha⟩ := hl.2 i
  obtain ⟨b, hb⟩ := hm.2 j
  refine ⟨a - b, ?_⟩
  push_cast at ha hb ⊢
  linarith

theorem half_ne {x : ℝ} (h : ∃ z : ℤ, x = z + 1 / 2) : x ≠ 0 := by
  obtain ⟨z, rfl⟩ := h
  intro h0
  have h1 : ((2 * z + 1 : ℤ) : ℝ) = 0 := by
    push_cast
    linarith
  have h2 : (2 * z + 1 : ℤ) = 0 := by exact_mod_cast h1
  omega

theorem half_ge {x : ℝ} (h : ∃ z : ℤ, x = z + 1 / 2) (hx : 0 < x) : 1 / 2 ≤ x := by
  obtain ⟨z, rfl⟩ := h
  have h1 : ((-1 : ℤ) : ℝ) < z := by
    push_cast
    linarith
  have hz : (-1 : ℤ) < z := by exact_mod_cast h1
  have hz0 : (0 : ℤ) ≤ z := by omega
  have h2 : (0 : ℝ) ≤ z := by exact_mod_cast hz0
  linarith

theorem inj_merge {lam : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hm : Formalism.QuantumDeterminants.IsHCParam mu) :
    Function.Injective (Sum.elim lam mu) := by
  intro x y hxy
  rcases x with i | j <;> rcases y with i' | j'
  · simp only [Sum.elim_inl] at hxy
    rw [hl.1.injective hxy]
  · simp only [Sum.elim_inl, Sum.elim_inr] at hxy
    exact absurd (sub_eq_zero.2 hxy) (half_ne (half hl hm i j'))
  · simp only [Sum.elim_inl, Sum.elim_inr] at hxy
    exact absurd (sub_eq_zero.2 hxy.symm) (half_ne (half hl hm i' j))
  · simp only [Sum.elim_inr] at hxy
    rw [hm.1.injective hxy]

section Step

variable {lam : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hm : Formalism.QuantumDeterminants.IsHCParam mu)
  {b : Fin (n + 1) ⊕ Fin n → ℕ} (hb : Mono lam mu b) {x : Fin (n + 1) ⊕ Fin n} (hx : 0 < b x)
  (hmin : ∀ y, 0 < b y → Sum.elim lam mu x ≤ Sum.elim lam mu y)
include hl hm hb hx hmin

theorem mono_down : Mono lam mu (Function.update b x (b x - 1)) := by
  intro y z hyz
  by_cases hy : y = x <;> by_cases hz : z = x
  · rw [hy, hz]
  · rw [hy, Function.update_self, Function.update_of_ne hz]
    have h := hb y z hyz
    rw [hy] at h
    omega
  · rw [hz, Function.update_of_ne hy, Function.update_self]
    rcases Nat.eq_zero_or_pos (b y) with h0 | hpos
    · omega
    · exfalso
      apply hy
      apply inj_merge hl hm
      rw [hz] at hyz
      exact le_antisymm hyz (hmin y hpos)
  · rw [Function.update_of_ne hy, Function.update_of_ne hz]
    exact hb y z hyz

theorem cond_down_l (s : Fin (n + 1)) (hs : x = Sum.inl s) (j : Fin n) : shL lam b s - 1 / 2 ≠ shM mu b j := by
  subst hs
  intro heq
  simp only [shL, shM, Pi.add_apply] at heq
  have hh := half hl hm s j
  rcases lt_trichotomy (mu j) (lam s) with hlt | heq' | hgt
  · have h1 := hb (Sum.inr j) (Sum.inl s) hlt.le
    have hge := half_ge hh (by linarith)
    have hc1 : (b (Sum.inr j) : ℝ) ≤ b (Sum.inl s) := by exact_mod_cast h1
    have hbeq : b (Sum.inr j) = b (Sum.inl s) := by
      have h2 : (b (Sum.inr j) : ℝ) = b (Sum.inl s) := by linarith
      exact_mod_cast h2
    have hpos : 0 < b (Sum.inr j) := by
      rw [hbeq]
      exact hx
    have h3 := hmin (Sum.inr j) hpos
    simp only [Sum.elim_inl, Sum.elim_inr] at h3
    linarith
  · exact half_ne hh (by linarith)
  · have h1 := hb (Sum.inl s) (Sum.inr j) hgt.le
    have hc1 : (b (Sum.inl s) : ℝ) ≤ b (Sum.inr j) := by exact_mod_cast h1
    linarith

theorem cond_down_m (j : Fin n) (hs : x = Sum.inr j) (s : Fin (n + 1)) : shM mu b j - 1 / 2 ≠ shL lam b s := by
  subst hs
  intro heq
  simp only [shL, shM, Pi.add_apply] at heq
  have hh : ∃ z : ℤ, mu j - lam s = z + 1 / 2 := by
    obtain ⟨z, hz⟩ := half hl hm s j
    exact ⟨-z - 1, by push_cast; linarith⟩
  rcases lt_trichotomy (lam s) (mu j) with hlt | heq' | hgt
  · have h1 := hb (Sum.inl s) (Sum.inr j) hlt.le
    have hge := half_ge hh (by linarith)
    have hc1 : (b (Sum.inl s) : ℝ) ≤ b (Sum.inr j) := by exact_mod_cast h1
    have hbeq : b (Sum.inl s) = b (Sum.inr j) := by
      have h2 : (b (Sum.inl s) : ℝ) = b (Sum.inr j) := by linarith
      exact_mod_cast h2
    have hpos : 0 < b (Sum.inl s) := by
      rw [hbeq]
      exact hx
    have h3 := hmin (Sum.inl s) hpos
    simp only [Sum.elim_inl, Sum.elim_inr] at h3
    linarith
  · exact half_ne hh (by linarith)
  · have h1 := hb (Sum.inr j) (Sum.inl s) hgt.le
    have hc1 : (b (Sum.inr j) : ℝ) ≤ b (Sum.inl s) := by exact_mod_cast h1
    linarith

end Step

theorem shL_down (lam : Fin (n + 1) → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) (s : Fin (n + 1)) (hx : 0 < b (Sum.inl s)) :
    shL lam (Function.update b (Sum.inl s) (b (Sum.inl s) - 1)) = shL lam b - Pi.single s 1 := by
  funext i
  simp only [shL, Pi.add_apply, Pi.sub_apply]
  by_cases h : i = s
  · subst h
    rw [Function.update_self, Pi.single_eq_same, Nat.cast_sub (by omega : 1 ≤ b (Sum.inl i))]
    push_cast
    ring
  · rw [Function.update_of_ne (fun h' => h (Sum.inl_injective h')), Pi.single_eq_of_ne h]
    ring

theorem shM_down_l (mu : Fin n → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) (s : Fin (n + 1)) :
    shM mu (Function.update b (Sum.inl s) (b (Sum.inl s) - 1)) = shM mu b := by
  funext j
  simp only [shM, Pi.add_apply]
  rw [Function.update_of_ne Sum.inr_ne_inl]

theorem shM_down (mu : Fin n → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) (j : Fin n) (hx : 0 < b (Sum.inr j)) :
    shM mu (Function.update b (Sum.inr j) (b (Sum.inr j) - 1)) = shM mu b - Pi.single j 1 := by
  funext i
  simp only [shM, Pi.add_apply, Pi.sub_apply]
  by_cases h : i = j
  · subst h
    rw [Function.update_self, Pi.single_eq_same, Nat.cast_sub (by omega : 1 ≤ b (Sum.inr i))]
    push_cast
    ring
  · rw [Function.update_of_ne (fun h' => h (Sum.inr_injective h')), Pi.single_eq_of_ne h]
    ring

theorem shL_down_m (lam : Fin (n + 1) → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) (j : Fin n) :
    shL lam (Function.update b (Sum.inr j) (b (Sum.inr j) - 1)) = shL lam b := by
  funext i
  simp only [shL, Pi.add_apply]
  rw [Function.update_of_ne Sum.inl_ne_inr]

theorem sum_down (b : Fin (n + 1) ⊕ Fin n → ℕ) (x : Fin (n + 1) ⊕ Fin n) (hx : 0 < b x) :
    ∑ y, Function.update b x (b x - 1) y + 1 = ∑ y, b y := by
  rw [Finset.sum_update_of_mem (mem_univ x), ← Finset.add_sum_erase _ _ (mem_univ x)]
  rw [show (univ \ {x} : Finset _) = univ.erase x from (Finset.erase_eq _ _).symm]
  omega

theorem down (hL : StepL) (hM : StepM) {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
    {mu : Fin n → ℝ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hG : Gp ε lam ε' mu e) :
    ∀ (k : ℕ) (b : Fin (n + 1) ⊕ Fin n → ℕ), ∑ y, b y = k → Mono lam mu b →
      OccAt ε (shL lam b) ε' (shM mu b) e → OccAt ε lam ε' mu e := by
  intro k
  induction k with
  | zero =>
    intro b hs _ ho
    have h0 : ∀ y, b y = 0 := fun y => (Finset.sum_eq_zero_iff.1 hs) y (mem_univ y)
    have e1 : shL lam b = lam := by funext i; simp [shL, h0]
    have e2 : shM mu b = mu := by funext i; simp [shM, h0]
    rwa [e1, e2] at ho
  | succ k ih =>
    intro b hs hb ho
    have hne : (univ.filter fun y => 0 < b y).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
      have : ∑ y, b y = 0 := Finset.sum_eq_zero fun y _ => by have := h (mem_univ y); omega
      omega
    obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image _ (Sum.elim lam mu) hne
    have hx' : 0 < b x := (mem_filter.1 hx).2
    have hmin' : ∀ y, 0 < b y → Sum.elim lam mu x ≤ Sum.elim lam mu y := fun y hy => hmin y (mem_filter.2 ⟨mem_univ y, hy⟩)
    have hb' := mono_down hG.hc hG.hc' hb hx' hmin'
    have hs' : ∑ y, Function.update b x (b x - 1) y = k := by have := sum_down b x hx'; omega
    refine ih _ hs' hb' ?_
    have hGb := gp_shift hG hb
    have hGb' := gp_shift hG hb'
    rcases x with s | j
    · rw [shL_down lam b s hx', shM_down_l] at hGb' ⊢
      exact hL n ε _ ε' _ e hGb s hGb' (cond_down_l hG.hc hG.hc' hb hx' hmin' s rfl) ho
    · rw [shM_down mu b j hx', shL_down_m] at hGb' ⊢
      exact hM n ε _ ε' _ e hGb j hGb' (cond_down_m hG.hc hG.hc' hb hx' hmin' j rfl) ho

theorem occurrence_of_walk (hL : StepL) (hM : StepM) (hB : Base) : Occ := by
  intro n ε lam ε' mu e hG hW
  obtain ⟨a, ha, ho⟩ := hB n ε lam ε' mu e hG hW
  exact down hL hM hG _ a rfl ha ho

end PositivityTheory.RgHe.Dec

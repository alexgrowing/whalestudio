import Formalism.SharpRestriction.Divisibility.OrbitPlaces

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.OrbitPlaces

def ydOf (f : ℕ → ℕ) (hf : Antitone f) (N : ℕ) : YoungDiagram where
  cells := (Finset.range N).biUnion fun r => (Finset.range (f r)).image fun c => (r, c)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_biUnion, Finset.coe_range, Finset.coe_image, Set.mem_iUnion, Set.mem_image, Set.mem_Iio,
      exists_prop] at ha ⊢
    obtain ⟨r, hr, c, hc, rfl⟩ := ha
    have h1 : b.1 ≤ r := (Prod.le_def.1 hba).1
    have h2 : b.2 ≤ c := (Prod.le_def.1 hba).2
    exact ⟨b.1, lt_of_le_of_lt h1 hr, b.2, lt_of_le_of_lt h2 (lt_of_lt_of_le hc (hf h1)), rfl⟩

theorem mem_ydOf (f : ℕ → ℕ) (hf : Antitone f) (N r c : ℕ) : (r, c) ∈ ydOf f hf N ↔ r < N ∧ c < f r := by
  rw [← YoungDiagram.mem_cells]
  simp only [ydOf, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨r', hr', c', hc', rfl, rfl⟩
    exact ⟨hr', hc'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨r, h1, c, h2, rfl, rfl⟩

theorem rowLen_ydOf (f : ℕ → ℕ) (hf : Antitone f) (N : ℕ) (h0 : ∀ r, N ≤ r → f r = 0) (r : ℕ) :
    (ydOf f hf N).rowLen r = f r := by
  have key : ∀ c, c < (ydOf f hf N).rowLen r ↔ c < f r := by
    intro c
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_ydOf]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    by_contra hr
    rw [h0 r (not_lt.1 hr)] at h
    exact absurd h (Nat.not_lt_zero _)
  apply le_antisymm
  · by_contra h
    exact absurd ((key _).1 (not_le.1 h)) (lt_irrefl _)
  · by_contra h
    exact absurd ((key _).2 (not_le.1 h)) (lt_irrefl _)

theorem colLen_ydOf (f : ℕ → ℕ) (hf : Antitone f) (N : ℕ) : (ydOf f hf N).colLen 0 ≤ N := by
  by_contra h
  have := (YoungDiagram.mem_iff_lt_colLen (μ := ydOf f hf N) (i := N) (j := 0)).2 (not_le.1 h)
  exact absurd ((mem_ydOf f hf N N 0).1 this).1 (lt_irrefl _)

def NuIsPart (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ τ : D.what₂.Tau, ∃ f : ℕ → ℕ, Antitone f ∧
    ∀ r, ((f r : ℕ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) τ r else 0

theorem nonempty_entries_of_partition (D : D7) (h : NuIsPart D) : Nonempty (Ent D) := by
  classical
  have key : ∀ (u : D.what₂.Word) (i : ℕ) (z : OrbitPlaces.Pl D), ∃ ν : YoungDiagram,
      (i < D.R.m → ∀ r, ((ν.rowLen r : ℕ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0) ∧
      ν.colLen 0 ≤ D.R.N i := by
    intro u i z
    by_cases hi : i < D.R.m
    · obtain ⟨f, hf, hr⟩ := h u i hi (tauPl D z)
      have h0 : ∀ r, D.R.N i ≤ r → f r = 0 := by
        intro r hN
        have := hr r
        rw [if_neg (not_lt.2 hN)] at this
        exact_mod_cast this
      exact ⟨ydOf f hf (D.R.N i), fun _ r => by rw [rowLen_ydOf f hf _ h0]; exact hr r, colLen_ydOf f hf _⟩
    · refine ⟨⊥, fun h' => absurd h' hi, ?_⟩
      by_contra hc
      have := (YoungDiagram.mem_iff_lt_colLen (μ := (⊥ : YoungDiagram)) (i := D.R.N i) (j := 0)).2 (not_le.1 hc)
      exact absurd this (YoungDiagram.notMem_bot _)
  choose ν h1 h2 using key
  exact ⟨{ nu := ν
           nu_row := fun u i hi z r => h1 u i z hi r
           nu_rows := h2
           Th := fun _ _ _ _ _ _ => 0
           ep := fun _ => 0
           be := fun _ _ => 0
           sg := fun _ _ => 0 }⟩

section NuPart

variable (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau)

def nuE (a : ℕ) : ℚ := if h : a < D.R.m then (D.hc τ).e ⟨a, h⟩ else 0

theorem nuE_step (a : ℕ) (h : a + 1 < D.R.m) : (D.R.t : ℚ) + 3 ≤ nuE D τ (a + 1) - nuE D τ a := by
  have ha : a < D.R.m := by omega
  have h1 : ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).e ⟨a + 1, h⟩ - (D.hc τ).b ⟨a + 1, h⟩ := (D.hc τ).gap_be ⟨a + 1, h⟩
  have h2 : ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨a + 1, h⟩ - (D.hc τ).e ⟨a, ha⟩ := (D.hc τ).gap_eb ⟨a, ha⟩ h
  unfold nuE
  rw [dif_pos h, dif_pos ha]
  linarith

theorem nuE_int (a : ℕ) : ∃ z : ℤ, nuE D τ a = z := by
  unfold nuE
  by_cases h : a < D.R.m
  · rw [dif_pos h]; exact (D.hc τ).e_int ⟨a, h⟩
  · rw [dif_neg h]; exact ⟨0, by simp⟩

def nuQ (i r : ℕ) : ℚ :=
  DV.srcPar D u τ r + nuE D τ i - (((D.R.N i : ℕ) : ℚ) + ((D.R.N (i + 1) : ℕ) : ℚ) - 1 - 2 * (r : ℚ)) / 2

theorem nuRow_eq (i r : ℕ) (hi : i < D.R.m) : DV.nuRow D u (i + 1) τ r = ((nuQ D u τ i r : ℚ) : ℝ) := by
  have hw : DV.wSz D (i + 1) τ = ((nuE D τ i : ℚ) : ℝ) := by
    unfold DV.wSz nuE
    rw [dif_pos ⟨by omega, by omega⟩, dif_pos hi]
    rfl
  unfold DV.nuRow nuQ
  rw [hw]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

theorem nuQ_lt (i r : ℕ) (hr : r < D.R.k) :
    nuQ D u τ i r = (D.hcW u τ).u ⟨r, hr⟩ + nuE D τ i - (D.R.k : ℚ) - (2 * (i : ℚ) + 1) * ((D.R.t : ℚ) + 1) / 2 + 1 / 2 + r := by
  unfold nuQ DV.srcPar Ranks.N
  rw [dif_pos hr]
  push_cast
  ring

theorem nu_div_lt (i r : ℕ) (hrN : r < D.R.N i) : (r - D.R.k) / (D.R.t + 1) < i ∨ r < D.R.k := by
  by_cases hk : r < D.R.k
  · exact Or.inr hk
  · left
    rw [Nat.div_lt_iff_lt_mul (show 0 < D.R.t + 1 by omega)]
    unfold Ranks.N at hrN
    omega

theorem nuQ_ge (i r : ℕ) (hi : i < D.R.m) (hk : D.R.k ≤ r) (hrN : r < D.R.N i) :
    nuQ D u τ i r = nuE D τ i - nuE D τ ((r - D.R.k) / (D.R.t + 1)) -
      ((i : ℚ) - (((r - D.R.k) / (D.R.t + 1) : ℕ) : ℚ)) * ((D.R.t : ℚ) + 1) := by
  have ha : (r - D.R.k) / (D.R.t + 1) < i := (nu_div_lt D i r hrN).resolve_right (not_lt.2 hk)
  have ham : (r - D.R.k) / (D.R.t + 1) < D.R.m := lt_trans ha hi
  have hdm : (D.R.t + 1) * ((r - D.R.k) / (D.R.t + 1)) + (r - D.R.k) % (D.R.t + 1) = r - D.R.k := Nat.div_add_mod _ _
  have hr : (r : ℚ) = (D.R.k : ℚ) + ((D.R.t : ℚ) + 1) * (((r - D.R.k) / (D.R.t + 1) : ℕ) : ℚ) +
      (((r - D.R.k) % (D.R.t + 1) : ℕ) : ℚ) := by
    have : r = D.R.k + ((D.R.t + 1) * ((r - D.R.k) / (D.R.t + 1)) + (r - D.R.k) % (D.R.t + 1)) := by omega
    have h2 : (r : ℚ) = ((D.R.k + ((D.R.t + 1) * ((r - D.R.k) / (D.R.t + 1)) + (r - D.R.k) % (D.R.t + 1)) : ℕ) : ℚ) :=
      congrArg (Nat.cast : ℕ → ℚ) this
    rw [h2]
    push_cast
    ring
  have he : nuE D τ ((r - D.R.k) / (D.R.t + 1)) = (D.hcW u τ).e ⟨(r - D.R.k) / (D.R.t + 1), ham⟩ := by
    unfold nuE
    rw [dif_pos ham, D.hcW_e u τ]
  unfold nuQ DV.srcPar Ranks.N
  rw [dif_neg (not_lt.2 hk), dif_pos ham, he]
  generalize (D.hcW u τ).e ⟨(r - D.R.k) / (D.R.t + 1), ham⟩ = E at *
  push_cast
  rw [hr]
  ring

theorem nu_u_step (r : ℕ) (h : r + 1 < D.R.k) :
    (D.hcW u τ).u ⟨r + 1, h⟩ + 1 ≤ (D.hcW u τ).u ⟨r, by omega⟩ := by
  have h1 : (D.hcW u τ).v ⟨r, by omega⟩ < (D.hcW u τ).u ⟨r, by omega⟩ := (D.hcW u τ).u_gt_v ⟨r, by omega⟩
  have h2 : (D.hcW u τ).u ⟨r + 1, h⟩ < (D.hcW u τ).v ⟨r, by omega⟩ := (D.hcW u τ).v_gt_u ⟨r, by omega⟩
  obtain ⟨z, hz⟩ := (D.hcW u τ).u_half ⟨r, by omega⟩
  obtain ⟨z', hz'⟩ := (D.hcW u τ).u_half ⟨r + 1, h⟩
  rw [hz] at h1
  rw [hz'] at h2
  rw [hz, hz']
  have h3 : (z' : ℚ) < z := by linarith
  have h4 : z' + 1 ≤ z := by exact_mod_cast h3
  have h5 : ((z' : ℚ) + 1) ≤ z := by exact_mod_cast h4
  linarith

theorem nu_last (hk : 0 < D.R.k) :
    ((D.R.t : ℚ) + 3) / 2 < (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ + nuE D τ 0 := by
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have h1 := (D.hcW u τ).u_last_gt hk hm
  have h2 := (D.hcW u τ).gap_be ⟨0, hm⟩
  have he : nuE D τ 0 = (D.hcW u τ).e ⟨0, hm⟩ := by
    unfold nuE
    rw [dif_pos hm, D.hcW_e u τ]
  rw [he]
  linarith

theorem nu_block_nonneg (i : ℕ) (hi : i < D.R.m) : ∀ d a : ℕ, a + d = i →
    0 ≤ nuE D τ i - nuE D τ a - ((i : ℚ) - (a : ℚ)) * ((D.R.t : ℚ) + 1) := by
  intro d
  induction d with
  | zero =>
    intro a h
    have : a = i := by omega
    subst this
    simp
  | succ d ih =>
    intro a h
    have h1 := ih (a + 1) (by omega)
    have h2 := nuE_step D τ a (by omega)
    push_cast at h1
    nlinarith

theorem nuQ_step (i r : ℕ) (hi : i < D.R.m) (h : r + 1 < D.R.N i) : nuQ D u τ i (r + 1) ≤ nuQ D u τ i r := by
  rcases lt_trichotomy (r + 1) D.R.k with hk | hk | hk
  · rw [nuQ_lt D u τ i (r + 1) hk, nuQ_lt D u τ i r (by omega)]
    have := nu_u_step D u τ r hk
    push_cast
    linarith
  · have hr : r < D.R.k := by omega
    rw [nuQ_lt D u τ i r hr, nuQ_ge D u τ i (r + 1) hi (by omega) h]
    have h0 : (r + 1 - D.R.k) / (D.R.t + 1) = 0 := by rw [hk]; simp
    rw [h0]
    have hl := nu_last D u τ (by omega)
    have hu : (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ = (D.hcW u τ).u ⟨r, hr⟩ := by
      congr 2
      omega
    rw [hu] at hl
    have hrk : (r : ℚ) + 1 = D.R.k := by exact_mod_cast hk
    push_cast
    nlinarith
  · have hk' : D.R.k ≤ r := by omega
    rw [nuQ_ge D u τ i (r + 1) hi (by omega) h, nuQ_ge D u τ i r hi hk' (by omega)]
    have hs : r + 1 - D.R.k = (r - D.R.k) + 1 := by omega
    have ha' : (r + 1 - D.R.k) / (D.R.t + 1) < i := (nu_div_lt D i (r + 1) h).resolve_right (by omega)
    rw [hs] at ha' ⊢
    rw [Nat.succ_div] at ha' ⊢
    split_ifs at ha' ⊢ with hd
    · have h2 := nuE_step D τ ((r - D.R.k) / (D.R.t + 1)) (by omega)
      push_cast
      nlinarith
    · simp

theorem nuQ_anti (i : ℕ) (hi : i < D.R.m) (r s : ℕ) (hrs : r ≤ s) (hs : s < D.R.N i) :
    nuQ D u τ i s ≤ nuQ D u τ i r := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s _ ih => exact (nuQ_step D u τ i s hi hs).trans (ih (by omega))

theorem nuQ_nonneg (i r : ℕ) (hi : i < D.R.m) (h : r < D.R.N i) : 0 ≤ nuQ D u τ i r := by
  have hkpos : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  by_cases hk : D.R.k ≤ r
  · rw [nuQ_ge D u τ i r hi hk h]
    have ha := (nu_div_lt D i r h).resolve_right (not_lt.2 hk)
    exact nu_block_nonneg D τ i hi (i - (r - D.R.k) / (D.R.t + 1)) _ (by omega)
  · have hkN : D.R.k - 1 < D.R.N i := by unfold Ranks.N; omega
    refine le_trans ?_ (nuQ_anti D u τ i hi r (D.R.k - 1) (by omega) hkN)
    rw [nuQ_lt D u τ i (D.R.k - 1) (by omega)]
    have hl := nu_last D u τ hkpos
    have hb := nu_block_nonneg D τ i hi i 0 (by omega)
    have hc : ((D.R.k - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hc]
    push_cast at hb
    nlinarith

theorem nuQ_int (i r : ℕ) (hi : i < D.R.m) (h : r < D.R.N i) : ∃ z : ℤ, nuQ D u τ i r = z := by
  obtain ⟨zi, hzi⟩ := nuE_int D τ i
  by_cases hk : D.R.k ≤ r
  · rw [nuQ_ge D u τ i r hi hk h]
    generalize (r - D.R.k) / (D.R.t + 1) = a
    obtain ⟨za, hza⟩ := nuE_int D τ a
    refine ⟨zi - za - ((i : ℤ) - (a : ℤ)) * ((D.R.t : ℤ) + 1), ?_⟩
    rw [hzi, hza]
    push_cast
    ring
  · have hr : r < D.R.k := not_le.1 hk
    rw [nuQ_lt D u τ i r hr]
    obtain ⟨z, hz⟩ := (D.hcW u τ).u_half ⟨r, hr⟩
    obtain ⟨c, hc⟩ := D.R.t_odd
    have hcq : (D.R.t : ℚ) = 2 * (c : ℚ) + 1 := by exact_mod_cast hc
    refine ⟨z + zi - (D.R.k : ℤ) - (2 * (i : ℤ) + 1) * ((c : ℤ) + 1) + 1 + (r : ℤ), ?_⟩
    rw [hz, hzi, hcq]
    push_cast
    ring

end NuPart

theorem nuIsPart (D : D7) : NuIsPart D := by
  intro u i hi τ
  refine ⟨fun r => if r < D.R.N i then ⌊nuQ D u τ i r⌋.toNat else 0, antitone_nat_of_succ_le fun r => ?_, fun r => ?_⟩
  · by_cases h : r + 1 < D.R.N i
    · simp only [if_pos h, if_pos (show r < D.R.N i by omega)]
      exact Int.toNat_le_toNat (Int.floor_le_floor (nuQ_step D u τ i r hi h))
    · simp only [if_neg h]
      exact Nat.zero_le _
  · by_cases h : r < D.R.N i
    · simp only [if_pos h]
      obtain ⟨z, hz⟩ := nuQ_int D u τ i r hi h
      have h0 := nuQ_nonneg D u τ i r hi h
      rw [hz] at h0
      have hz0 : 0 ≤ z := by exact_mod_cast h0
      rw [nuRow_eq D u τ i r hi, hz, Int.floor_intCast]
      have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
      have h2 : ((z.toNat : ℕ) : ℝ) = ((z : ℤ) : ℝ) := by exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) this
      rw [h2]
      push_cast
      rfl
    · simp only [if_neg h]
      simp

theorem nonempty_entries (D : D7) : Nonempty (Ent D) := nonempty_entries_of_partition D (nuIsPart D)

theorem nuPart_of_Ent {D : D7} (E : Ent D) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (z : OrbitPlaces.Pl D) :
    ∃ f : ℕ → ℕ, Antitone f ∧
      ∀ r, ((f r : ℕ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0 :=
  ⟨(E.nu u i z).rowLen, fun a b hab => (E.nu u i z).rowLen_anti a b hab, E.nu_row u i hi z⟩

end Formalism.MainNotions.DIV.Inh

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepParametersPartitionExtendedByZeros
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColParam

open GlobalTheory.Grid Finset

section GridFacts

variable (D : D7) (τ : D.what₂.Tau)

local notation "Γ" => grid D τ

theorem e_eq {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).e l : ℤ) : ℚ) = (D.hc τ).e ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩

theorem b_eq {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).b l : ℤ) : ℚ) = (D.hc τ).b ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩

theorem v_eq {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : (((Γ).v i : ℤ) : ℚ) = (D.hc τ).v ⟨i - 2, by omega⟩ := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  exact GlobalTheory.SignedHC.GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩

theorem be {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).e l : ℚ) - (Γ).b l := by
  rw [e_eq D τ h1 h2, b_eq D τ h1 h2]
  exact (D.hc τ).gap_be _

theorem eb {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).b (l + 1) : ℚ) - (Γ).e l := by
  rw [e_eq D τ h1 (by omega), b_eq D τ (by omega) h2]
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact (D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))

theorem e_lt {l l' : ℕ} (h1 : 1 ≤ l) (h : l < l') (h2 : l' ≤ D.R.m) : (D.R.t : ℚ) + 3 + (Γ).e l ≤ (Γ).e l' := by
  induction l', h using Nat.le_induction with
  | base =>
    linarith [be D τ (l := l + 1) (by omega) h2, eb D τ h1 h2]
  | succ n hn ih =>
    have := ih (by omega)
    have e1 := be D τ (l := n + 1) (by omega) h2
    have e2 := eb D τ (l := n) (by omega) h2
    have : (0 : ℚ) ≤ D.R.t := by positivity
    linarith

theorem cloud_ge {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : -((Γ).b 1 : ℚ) + 1 ≤ (Γ).v i := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k := by
    rw [v_eq D τ hk le_rfl, b_eq D τ le_rfl hm]
    have e1 := (D.hc τ).u_last_gt (by omega) (by omega)
    have e2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
    simp only [e3] at e2
    exact e1.trans e2
  have base' : -((Γ).b 1) < (Γ).v D.R.k := by exact_mod_cast base
  have step : (Γ).v D.R.k ≤ (Γ).v i := by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact ((Γ).v_anti i D.R.k h1 h le_rfl).le
  have : -((Γ).b 1) + 1 ≤ (Γ).v i := by omega
  exact_mod_cast this

theorem a_le {i j : ℕ} (h : i ≤ j) : (Γ).a j ≤ (Γ).a i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · have : (0 : ℚ) ≤ (Γ).ga := by positivity
    linarith [GlobalTheory.ChiGrid.a_add_le (G := Γ) h]

theorem blockMPlus_bd {l : ℕ} {x : ℚ} (h : x ∈ (Γ).blockMPlus l) :
    -((Γ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x ∧ x ≤ -((Γ).e l : ℚ) + (D.R.t : ℚ) / 2 := by
  have := abs_le.1 (GlobalTheory.SignedHC.abs_sub_le_of_mem_block h)
  have e : (((Γ).t + 1 : ℕ) : ℚ) = D.R.t + 1 := by push_cast; rfl
  rw [e] at this
  constructor <;> linarith [this.1, this.2]

theorem s_lt_gap : (Γ).s < (Γ).ga := by
  have := (isLeast_gap D).1.2.1
  show sLen D < gap D
  omega

theorem gridDataAtRealPlace_s_odd : Odd (Γ).s := GlobalTheory.ChiGrid.odd_sLen D

theorem weightX_above {j : ℕ} (hj : j + 1 ≤ D.R.m) {x y : ℚ} (hx : x ∈ (Γ).weightX j)
    (hy : y ∈ (Γ).blockMPlus (j + 1)) : y < x := by
  have hm : 1 ≤ D.R.m := by omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have hg : (0 : ℚ) ≤ (Γ).ga := by positivity
  obtain ⟨y1, y2⟩ := blockMPlus_bd D τ hy
  have hbe := be D τ (l := 1) le_rfl hm
  have he1 : ((Γ).e 1 : ℚ) ≤ (Γ).e (j + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact le_rfl
    · linarith [e_lt D τ (l := 1) (l' := j + 1) le_rfl (by omega) hj]
  have hlow : y < -((Γ).b 1 : ℚ) := by linarith
  have hc2 := cloud_ge D τ (i := 2) le_rfl hk
  have ham : (Γ).a (Γ).m = (Γ).v 2 + (Γ).ga + 1 / 2 := (Γ).a_m
  rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
    linarith [a_le D τ hi]
  · obtain ⟨i, h1, h2, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
    have := cloud_ge D τ h1 h2
    simp only [GlobalTheory.SignedHC.GridData.vHalf]
    linarith
  · have := (GlobalTheory.ChiGrid.blockC'_between (grid_nearMid D τ) (gridDataAtRealPlace_s_odd D τ).pos (s_lt_gap D τ) h1 h2 h).1
    linarith [a_le D τ h2]
  · have := e_lt D τ h1 (by omega : l < j + 1) hj
    have := (blockMPlus_bd D τ h).1
    linarith

theorem inCoset_weightX (j : ℕ) : GlobalTheory.SignedHC.InCoset (1 / 2) ((Γ).weightX j) := by
  induction j with
  | zero => exact GlobalTheory.ChiGrid.inCoset_weightX_zero (gridDataAtRealPlace_s_odd D τ)
  | succ j ih =>
    rw [(Γ).weightX_succ]
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact ih x h
    · obtain ⟨a, -, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
      obtain ⟨u, hu⟩ := D.R.t_odd
      have e : ((Γ).t : ℚ) = 2 * u + 1 := by
        have : ((Γ).t : ℚ) = D.R.t := rfl
        rw [this, hu]; push_cast; ring
      refine ⟨-(Γ).e (j + 1) + u - a, ?_⟩
      push_cast
      rw [e]
      ring

theorem card_weightX {j : ℕ} (hj : j ≤ D.R.m) : ((Γ).weightX j).card = GlobalTheory.ChiGrid.rankX D j := by
  induction j with
  | zero =>
    rw [GlobalTheory.ChiGrid.card_weightX_zero (grid_nearMid D τ) (gridDataAtRealPlace_s_odd D τ).pos (s_lt_gap D τ)]
    simp [GlobalTheory.ChiGrid.rankX]; rfl
  | succ j ih =>
    rw [(Γ).weightX_succ, card_union_of_disjoint
      (disjoint_left.2 fun x hx hy => (weightX_above D τ hj hx hy).ne rfl), ih (by omega)]
    have : ((Γ).blockMPlus (j + 1)).card = D.R.t + 1 := GlobalTheory.SignedHC.card_block _ _
    rw [this]
    simp only [GlobalTheory.ChiGrid.rankX]
    ring

end GridFacts

theorem enum_plus {n : ℕ} {E : Finset ℚ} {lam : Fin n → ℝ} {ε : Fin n → Bool}
    (h : Formalism.L2.Theta.IsEnum (GlobalTheory.SignedHC.plus E) lam ε) :
    ε = Formalism.MainNotions.S.allPos n ∧ E.card = n ∧ ∀ x : ℝ, x ∈ Set.range lam ↔ ∃ y ∈ E, x = (y : ℝ) := by
  obtain ⟨hl, q, hq, hS⟩ := h
  have hmem : ∀ a, q a ∈ E ∧ ε a = true := fun a => by
    have : (q a, ε a) ∈ GlobalTheory.SignedHC.plus E := by rw [hS]; exact mem_image_of_mem _ (mem_univ a)
    exact GlobalTheory.SignedHC.mem_plus.1 this
  have hinj : Function.Injective fun a => (q a, ε a) := by
    intro a b hab
    have h1 : q a = q b := congrArg Prod.fst hab
    apply hl.injective
    rw [hq, hq, h1]
  refine ⟨funext fun a => by rw [(hmem a).2]; rfl, ?_, ?_⟩
  · have h1 : (GlobalTheory.SignedHC.plus E).card = E.card :=
      card_image_of_injective _ (fun x y h => congrArg Prod.fst h)
    rw [← h1, hS, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  · intro x
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨q a, (hmem a).1, hq a⟩
    · rintro ⟨y, hy, rfl⟩
      have : (y, true) ∈ GlobalTheory.SignedHC.plus E := GlobalTheory.SignedHC.mem_plus.2 ⟨hy, rfl⟩
      rw [hS] at this
      obtain ⟨a, -, ha⟩ := mem_image.1 this
      exact ⟨a, by rw [hq]; congr 1; exact congrArg Prod.fst ha⟩

theorem shape_below {n T : ℕ} (c : ℝ) (lam : Fin n → ℝ) (hl : StrictAnti lam) (hb : ∀ a, c < lam a)
    (lam' : Fin (n + T) → ℝ) (h' : StrictAnti lam')
    (hr : ∀ x : ℝ, x ∈ Set.range lam' ↔ x ∈ Set.range lam ∨ ∃ d : ℕ, d < T ∧ x = c - d) (b : Fin (n + T)) :
    lam' b = if h : (b : ℕ) < n then lam ⟨b, h⟩ else c - (((b : ℕ) - n : ℕ) : ℝ) := by
  let L : Fin (n + T) → ℝ := fun b => if h : (b : ℕ) < n then lam ⟨b, h⟩ else c - (((b : ℕ) - n : ℕ) : ℝ)
  have hL : StrictAnti L := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    simp only [L]
    split_ifs with h1 h2 h2
    · exact hl (Fin.mk_lt_mk.2 hab')
    · omega
    · have := hb ⟨a, h2⟩
      have : (0 : ℝ) ≤ (((b : ℕ) - n : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · have : (((a : ℕ) - n : ℕ) : ℝ) < (((b : ℕ) - n : ℕ) : ℝ) := by exact_mod_cast (by omega : (a : ℕ) - n < b - n)
      linarith
  have key : lam' = L := by
    rw [← StrictAnti.range_inj h' hL]
    ext x
    rw [hr]
    constructor
    · rintro (⟨a, rfl⟩ | ⟨d, hd, rfl⟩)
      · refine ⟨⟨a, by omega⟩, ?_⟩
        simp [L]
      · refine ⟨⟨n + d, by omega⟩, ?_⟩
        simp [L]
    · rintro ⟨b, rfl⟩
      by_cases hb' : (b : ℕ) < n
      · exact .inl ⟨⟨b, hb'⟩, by simp [L, hb']⟩
      · exact .inr ⟨(b : ℕ) - n, by omega, by simp [L, hb']⟩
  rw [key]

theorem colPar : ∀ (D : D7) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) (n N : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool) (lam' : Fin N → ℝ) (ε' : Fin N → Bool), Formalism.L2.Theta.IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.L2.Theta.IsEnum (GlobalTheory.Grid.parXp D (j + 1) τ) lam' ε' → ε = Formalism.MainNotions.S.allPos n ∧ ε' = Formalism.MainNotions.S.allPos N ∧ ∃ x₁ x₃ : ℤ, (x₁ : ℚ) = -(D.hc τ).e ⟨j, hj⟩ + (n : ℚ) / 2 ∧ (x₃ : ℚ) = -((N : ℚ) / 2 + -(D.hc τ).e ⟨j, hj⟩) ∧ ∃ (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν ∧ (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lam a = -(x₃ : ℝ) + ν (Fin.castLE hn a)) ∧ ∀ b, Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos N) lam' b = (x₁ : ℝ) + ν b := by
  intro D j hj τ n N lam ε lam' ε' hE hE'
  have hj' : j + 1 ≤ D.R.m := hj
  obtain ⟨s, hs⟩ := D.R.t_odd
  have htR : (D.R.t : ℝ) = 2 * s + 1 := by rw [hs]; push_cast; ring
  have htQ : (D.R.t : ℚ) = 2 * s + 1 := by rw [hs]; push_cast; ring
  set e : ℤ := (grid D τ).e (j + 1) with he_def
  have hce : (e : ℚ) = (D.hc τ).e ⟨j, hj⟩ := by
    have := e_eq D τ (l := j + 1) (by omega) hj'
    simp only [Nat.add_sub_cancel] at this
    exact this
  have hB : (grid D τ).blockMPlus (j + 1) = TPar.block (-(e : ℚ)) (D.R.t + 1) := rfl
  have hX : parXp D j τ = GlobalTheory.SignedHC.plus ((grid D τ).weightX j) := rfl
  have hX' : parXp D (j + 1) τ =
      GlobalTheory.SignedHC.plus ((grid D τ).weightX j ∪ TPar.block (-(e : ℚ)) (D.R.t + 1)) := by
    show GlobalTheory.SignedHC.plus ((grid D τ).weightX (j + 1)) = _
    rw [(grid D τ).weightX_succ, hB]
  rw [hX] at hE
  rw [hX'] at hE'
  obtain ⟨hε, hcard, hr⟩ := enum_plus hE
  obtain ⟨hε', hcard', hr'⟩ := enum_plus hE'
  have htop : -(e : ℚ) + (D.R.t : ℚ) / 2 ∈ (grid D τ).blockMPlus (j + 1) := by
    rw [hB]; exact GlobalTheory.SignedHC.mem_block.2 ⟨0, by omega, by push_cast; ring⟩
  have habove : ∀ x ∈ (grid D τ).weightX j, -(e : ℚ) + (D.R.t : ℚ) / 2 + 1 ≤ x := by
    intro x hx
    have hlt := weightX_above D τ hj' hx htop
    obtain ⟨z, hz⟩ := inCoset_weightX D τ j x hx
    rw [hz, htQ] at hlt ⊢
    have : ((-e + s : ℤ) : ℚ) < z := by push_cast; linarith
    have h2 : -e + s < z := by exact_mod_cast this
    have h3 : ((-e + s + 1 : ℤ) : ℚ) ≤ z := by exact_mod_cast Int.add_one_le_iff.2 h2
    push_cast at h3
    linarith
  have hdisj : Disjoint ((grid D τ).weightX j) (TPar.block (-(e : ℚ)) (D.R.t + 1)) :=
    disjoint_left.2 fun x hx hy => (weightX_above D τ hj' hx (by rw [hB]; exact hy)).ne rfl
  have hN : N = n + (D.R.t + 1) := by
    rw [← hcard', card_union_of_disjoint hdisj, hcard, GlobalTheory.SignedHC.card_block]
  have hne : Even n := by
    rw [← hcard, card_weightX D τ (by omega)]; exact GlobalTheory.ChiGrid.even_rankX D j
  subst hN
  refine ⟨hε, hε', ?_⟩
  obtain ⟨p, hp⟩ := hne
  have hpR : (n : ℝ) = 2 * p := by rw [hp]; push_cast; ring
  have hpQ : (n : ℚ) = 2 * p := by rw [hp]; push_cast; ring
  have hz0 : ∀ a, ∃ z : ℤ, lam a = (z : ℝ) + 1 / 2 := fun a => by
    obtain ⟨y, hy, hya⟩ := (hr (lam a)).1 ⟨a, rfl⟩
    obtain ⟨z, hz⟩ := inCoset_weightX D τ j y hy
    exact ⟨z, by rw [hya, hz]; push_cast; ring⟩
  choose z hz using hz0
  have hzb : ∀ a, -e + s + 1 ≤ z a := fun a => by
    obtain ⟨y, hy, hya⟩ := (hr (lam a)).1 ⟨a, rfl⟩
    have h1 := habove y hy
    have h3 : ((-(e : ℚ) + (D.R.t : ℚ) / 2 + 1 : ℚ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast h1
    push_cast at h3
    rw [htR, ← hya, hz] at h3
    have h4 : ((-e + s + 1 : ℤ) : ℝ) ≤ z a := by push_cast; linarith
    exact_mod_cast h4
  have hzanti : StrictAnti z := fun a b hab => by
    have := hE.1 hab
    rw [hz, hz] at this
    have : (z b : ℝ) < z a := by linarith
    exact_mod_cast this
  set c : ℝ := -(e : ℝ) + s + 1 / 2 with hc
  have hshape := shape_below c lam hE.1 (fun a => by
      have := hzb a
      have h : ((-e + s + 1 : ℤ) : ℝ) ≤ z a := by exact_mod_cast this
      push_cast at h
      rw [hz, hc]; linarith) lam' hE'.1 (fun x => by
      rw [hr' x, hr x]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases mem_union.1 hy with hy | hy
        · exact .inl ⟨y, hy, rfl⟩
        · obtain ⟨d, hd, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 hy
          refine .inr ⟨d, hd, ?_⟩
          push_cast
          rw [htR, hc]; ring
      · rintro (⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩)
        · exact ⟨y, mem_union_left _ hy, rfl⟩
        · refine ⟨-(e : ℚ) + (((D.R.t + 1 : ℕ) : ℚ) - 1) / 2 - d,
            mem_union_right _ (GlobalTheory.SignedHC.mem_block.2 ⟨d, hd, rfl⟩), ?_⟩
          push_cast
          rw [htR, hc]; ring)
  let ν : Fin (n + (D.R.t + 1)) → ℕ := fun b =>
    if h : (b : ℕ) < n then (z ⟨b, h⟩ + (b : ℕ) + e - n - s).toNat else 0
  have hmono : ∀ a b : Fin n, a ≤ b → z b + (b : ℕ) ≤ z a + (a : ℕ) := fun a b hab => by
    have := GlobalTheory.LastStepParam.sub_mono' (z := fun a => -z a) (fun x y hxy => by simpa using hzanti hxy) hab
    try simp only at this
    omega
  have hpos : ∀ a : Fin n, 0 ≤ z a + (a : ℕ) + e - n - s := fun a => by
    have ha := a.2
    have h1 := hmono a ⟨n - 1, by omega⟩ (Fin.mk_le_mk.2 (by omega) : (⟨a, a.2⟩ : Fin n) ≤ ⟨n - 1, by omega⟩)
    have h2 := hzb ⟨n - 1, by omega⟩
    try simp only at h1
    omega
  have hν : ∀ (b : Fin (n + (D.R.t + 1))) (h : (b : ℕ) < n), (ν b : ℝ) = z ⟨b, h⟩ + ((b : ℕ) : ℝ) + e - n - s := by
    intro b h
    have : ((ν b : ℕ) : ℤ) = z ⟨b, h⟩ + (b : ℕ) + e - n - s := by
      simp only [ν, dif_pos h]
      exact Int.toNat_of_nonneg (hpos ⟨b, h⟩)
    have : ((ν b : ℕ) : ℝ) = ((z ⟨b, h⟩ + (b : ℕ) + e - n - s : ℤ) : ℝ) := by exact_mod_cast this
    rw [this]; push_cast; ring
  refine ⟨-e + p, e - p - s - 1, ?_, ?_, by omega, ν, ?_, ?_, ?_, ?_⟩
  · rw [← hce]; push_cast; rw [hpQ]; ring
  · rw [← hce]; push_cast; rw [hpQ, htQ]; ring
  · intro c d hcd
    have hcd' : (c : ℕ) ≤ d := hcd
    simp only [ν]
    split_ifs with h1 h2 h2
    all_goals first
      | exact Nat.zero_le _
      | exact le_rfl
      | omega
      | (apply Int.toNat_le_toNat
         have := hmono ⟨c, by omega⟩ ⟨d, by omega⟩ (Fin.mk_le_mk.2 hcd')
         try simp only at this
         omega)
  · intro b hb
    simp only [ν]
    rw [dif_neg (by omega)]
  · intro a
    have e1 := hν (Fin.castLE (by omega) a) a.2
    rw [GlobalTheory.LastStepParam.lowK_allPos, e1, hz a]
    simp only [Fin.val_castLE, Fin.eta]
    push_cast
    linarith [hpR]
  · intro b
    rw [GlobalTheory.LastStepParam.lowK_allPos, hshape b]
    by_cases hb : (b : ℕ) < n
    · rw [dif_pos hb, hz, hν b hb]
      push_cast
      linarith [hpR, htR]
    · have h0 : ν b = 0 := by simp only [ν]; rw [dif_neg hb]
      rw [dif_neg hb, h0, Nat.cast_sub (by omega)]
      push_cast
      linarith [hpR, htR]

end GlobalTheory.ColParam

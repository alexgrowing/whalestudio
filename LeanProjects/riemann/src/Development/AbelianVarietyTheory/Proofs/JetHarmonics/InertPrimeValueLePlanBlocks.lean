import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSumsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBoundStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypings

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators

namespace GlobalTheory.PlanValue

theorem bg_add {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (i : ℕ) (hi : Odd i) :
    RF.bg (a + (i : ZMod d)) = 1 - RF.bg a := by
  have h : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    rw [ZMod.val_add, ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ hd.two_dvd, Nat.add_mod,
      Nat.mod_mod_of_dvd _ hd.two_dvd, Nat.odd_iff.1 hi]
    omega
  unfold RF.bg
  by_cases ha : Even a.val
  · rw [if_pos ha, if_neg (by rw [h]; simpa using ha)]; rfl
  · rw [if_neg ha, if_pos (h.2 ha)]; rfl

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem big_bg (X : RowData C V d I J) (h : X.Alt) (a : ZMod d) : X.big (RF.bg a) a := by
  unfold RF.bg
  split_ifs with ha
  · exact (h.2 a).2 ha
  · exact (X.big_compl 0 a).2 fun hb => ha ((h.2 a).1 hb)

theorem rk_le (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) : X.rkF g a ≤ X.n + (X.j + X.j') := by
  by_cases h : X.big g a
  · have : X.rkF g a = _ := X.rk_big g a h
    omega
  · have : X.rkF g a = _ := X.rk_small g a h
    omega

def rst (n : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) (g : Fin 2) (a : ZMod d) (k : ℕ) : ℕ :=
  if g = RF.bg a ∧ k = n then 0 else ga g a k

theorem deg_le (X : RowData C V d I J) (n K : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    RF.monDegAll X 0 (rst n ga 0) K + RF.monDegAll X 1 (rst n ga 1) K ≤ RF.restDeg RF.bg n ga K := by
  have key : ∀ g, RF.monDegAll X g (rst n ga g) K ≤
      ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, if g = RF.bg a ∧ k = n then 0 else k * ga g a k := by
    intro g
    unfold RF.monDegAll monDeg
    refine Finset.sum_le_sum (N := ℕ) fun a _ => ?_
    refine le_trans (Finset.sum_le_sum_of_subset (M := ℕ)
      (Finset.Icc_subset_Icc_right (min_le_left K _))) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold rst
    split_ifs <;> simp
  unfold RF.restDeg
  rw [Fin.sum_univ_two]
  convert Nat.add_le_add (key 0) (key 1)

noncomputable def supp {l : ℕ} {W : ZMod d → ℕ} (p : Plan l d W) : Finset (ZMod d × ℕ) :=
  (Finset.univ ×ˢ oddLevels d).filter fun x => p.y x.1 x.2 ≠ 0

theorem sum_supp {M : Type} [AddCommMonoid M] {l : ℕ} {W : ZMod d → ℕ} (p : Plan l d W) (f : ZMod d → ℕ → ℕ → M)
    (hf : ∀ a i, f a i 0 = 0) :
    ∑ x ∈ supp p, f x.1 x.2 (p.y x.1 x.2) = ∑ a, ∑ i ∈ oddLevels d, f a i (p.y a i) := by
  rw [← Finset.sum_product']
  unfold supp
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h
  · rfl
  · rw [not_not.1 h, hf]

theorem card_supp {l : ℕ} {W : ZMod d → ℕ} (p : Plan l d W) (N : ℕ) (h : ∀ a i, N ≤ i → p.y a i = 0) :
    (supp p).card ≤ d * (N - 1) := by
  have : supp p ⊆ Finset.univ ×ˢ Finset.Ico 1 N := by
    intro x hx
    simp only [supp, oddLevels, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Ico]
    refine ⟨hx.1.2.pos, ?_⟩
    by_contra hc
    exact hx.2 (h _ _ (not_lt.1 hc))
  simpa [ZMod.card] using Finset.card_le_card this

noncomputable def blocks {W : ZMod d → ℕ} (X : RowData C V d I J) (p : Plan V.l d W) (ga : Fin 2 → ZMod d → ℕ → ℕ)
    (K : ℕ) : List (RF.GlobalTheory d × ℝ) :=
  (RF.GlobalTheory.mon 0 (rst X.n ga 0) K, (RF.monDegAll X 0 (rst X.n ga 0) K : ℝ) / ((V.l : ℝ) - 1)) ::
  (RF.GlobalTheory.mon 1 (rst X.n ga 1) K, (RF.monDegAll X 1 (rst X.n ga 1) K : ℝ) / ((V.l : ℝ) - 1)) ::
  (((Finset.univ : Finset (ZMod d)).toList.map fun a =>
      (RF.GlobalTheory.ch (RF.bg a) a (p.u a), RF.chBd V.l X.n X.m (p.u a))) ++
    ((supp p).toList.map fun x =>
      (RF.GlobalTheory.bi (RF.bg x.1) x.1 x.2 (p.y x.1 x.2), RF.blockBd V.l X.n X.m x.2 (p.y x.1 x.2))))

theorem blocks_rows {W : ZMod d → ℕ} (X : RowData C V d I J) (p : Plan V.l d W) (ga : Fin 2 → ZMod d → ℕ → ℕ)
    (K N : ℕ) (hN : 1 ≤ N) (h : ∀ a i, N ≤ i → p.y a i = 0) :
    ((blocks X p ga K).map fun q => q.1.what₂ X.n).sum ≤ d * (N * X.n) + 2 * K := by
  simp only [blocks, List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
    Finset.sum_map_toList, Function.comp_def, RF.GlobalTheory.what₂, Finset.sum_const, smul_eq_mul, Finset.card_univ, ZMod.card]
  have h1 := Nat.mul_le_mul_right X.n (card_supp p N h)
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h1
  nlinarith

theorem blocks_bd {W : ZMod d → ℕ} (X : RowData C V d I J) (p : Plan V.l d W) (ga : Fin 2 → ZMod d → ℕ → ℕ)
    (K : ℕ) (hl : 2 ≤ V.l) :
    ((blocks X p ga K).map Prod.snd).sum ≤
      p.bound X.n X.m + (RF.restDeg RF.bg X.n ga K : ℝ) / ((V.l : ℝ) - 1) := by
  have hl' : (0 : ℝ) < (V.l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ V.l := by exact_mod_cast hl
    linarith
  simp only [blocks, List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
    Finset.sum_map_toList, Function.comp_def]
  rw [sum_supp p (fun _ i y => RF.blockBd V.l X.n X.m i y) (fun _ _ => by simp [RF.blockBd])]
  have h : ((RF.monDegAll X 0 (rst X.n ga 0) K : ℝ) + RF.monDegAll X 1 (rst X.n ga 1) K) ≤
      RF.restDeg RF.bg X.n ga K := by exact_mod_cast deg_le X X.n K ga
  have h' := div_le_div_of_nonneg_right h hl'.le
  rw [add_div] at h'
  have e : p.bound X.n X.m = (∑ a, ∑ i ∈ oddLevels d, RF.blockBd V.l X.n X.m i (p.y a i)) +
    ∑ a, RF.chBd V.l X.n X.m (p.u a) := rfl
  rw [e]
  linarith

theorem blocks_wt {W : ZMod d → ℕ} (X : RowData C V d I J) (hX : X.Alt) (p : Plan V.l d W)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) (hK : X.n + (X.j + X.j') ≤ K)
    (hs : ∀ g a k, ga g a k ≠ 0 → 1 ≤ k ∧ k ≤ X.rkF g a) (hm : ∀ a, ga (RF.bg a) a X.n = W a)
    (g : Fin 2) (a : ZMod d) (k : ℕ) :
    ((blocks X p ga K).map fun q => q.1.wt X g a k).sum = ga g a k := by
  simp only [blocks, List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map,
    Finset.sum_map_toList, Function.comp_def, RF.GlobalTheory.wt]
  rw [sum_supp p (fun b i y => (if g = RF.bg b ∧ a = b ∧ k = X.n then V.l ^ i * y else 0) +
    (if g = 1 - RF.bg b ∧ a = b + (i : ZMod d) ∧ k = X.n then y else 0)) (fun _ _ => by simp)]
  have hmon : ∀ g', (if g = g' ∧ 1 ≤ k ∧ k ≤ min K (X.rkF g' a) then rst X.n ga g' a k else 0) =
      if g = g' then rst X.n ga g a k else 0 := by
    intro g'
    by_cases hg : g = g'
    · subst hg
      have := rk_le X g a
      by_cases h0 : ga g a k = 0
      · simp [rst, h0]
      · have := hs g a k h0
        rw [if_pos ⟨rfl, by omega, by omega⟩, if_pos rfl]
    · simp [hg]
  have hmon2 : (if g = 0 then rst X.n ga g a k else 0) + (if g = 1 then rst X.n ga g a k else 0) =
      rst X.n ga g a k := by fin_cases g <;> simp
  rw [hmon, hmon, ← add_assoc, hmon2]
  have h2 : ∑ b, ∑ i ∈ oddLevels d, (if g = 1 - RF.bg b ∧ a = b + (i : ZMod d) ∧ k = X.n then p.y b i else 0) =
      ∑ i ∈ oddLevels d, if g = RF.bg a ∧ k = X.n then p.y (a - (i : ZMod d)) i else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : Odd i := (Finset.mem_filter.1 hi).2
    rw [Finset.sum_eq_single (a - (i : ZMod d))]
    · rw [← bg_add hX.1 _ i hi']; simp
    · intro b _ hb
      rw [if_neg]
      rintro ⟨-, h, -⟩
      exact hb (by rw [h]; simp)
    · simp
  have h1 : ∑ b, ∑ i ∈ oddLevels d, (if g = RF.bg b ∧ a = b ∧ k = X.n then V.l ^ i * p.y b i else 0) =
      ∑ i ∈ oddLevels d, if g = RF.bg a ∧ k = X.n then V.l ^ i * p.y a i else 0 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  have h3 : ∑ b, (if g = RF.bg b ∧ a = b ∧ k = X.n then p.u b else 0) =
      if g = RF.bg a ∧ k = X.n then p.u a else 0 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  simp only [Finset.sum_add_distrib]
  rw [h1, h2, h3]
  by_cases hc : g = RF.bg a ∧ k = X.n
  · obtain ⟨rfl, rfl⟩ := hc
    simp only [rst, and_self, if_true]
    rw [hm a, p.bal a]
    ring
  · simp [rst, hc]

theorem card_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) : Z.card * P.d = Fintype.card P.Pl := by
  classical
  rw [← Finset.card_univ]
  have : Z.card * P.d = (Z ×ˢ (Finset.univ : Finset (ZMod P.d))).card := by simp [ZMod.card]
  rw [this]
  refine Finset.card_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩
      ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

theorem val_le_plan : ∀ (P : RF.Par) (l : ℕ) (C1 : ℝ), ParOK P → 5 ≤ l → ∀ (Pk : RF.PkgInert P l C1) (p : ∀ z, Plan l P.d (RF.alongOrb P z Pk.W)),
    (∀ z ∈ Pk.Z, ∀ a i, i0 P.k l ≤ i → (p z).y a i = 0) →
    (∀ z ∈ Pk.Z, ∀ a i, (p z).y a i ≠ 0 → (RF.GlobalTheory.bi (RF.bg a) a i ((p z).y a i)).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m i ((p z).y a i))) →
    Pk.ν ≤ (∑ z ∈ Pk.Z, (p z).bound (P.k - 1) P.m) + Pk.rest / ((l : ℝ) - 1) := by
  intro P l C1 hP hl Pk p hlev hatt
  obtain ⟨⟨C, V, hVl, I, J, X, F, hn⟩, Z, hZ, alt, ga, W, nW, T, θ0, rest, ν, wt, what₂, deg, val⟩ := Pk
  subst hVl
  dsimp only at *
  revert hlev hatt
  revert p
  change ∀ p : ∀ z, Plan V.l P.d (RF.alongOrb P z W), _
  intro p hlev hatt
  have hk := hP.mk_le
  have hi0 : 1 ≤ i0 P.k V.l := by
    have := (GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 P.k V.l (by omega) (by omega)).2.1
    omega
  have key := val (fun z => blocks (X z) (p z) (ga z) P.r) ?_ ?_ ?_
  · refine key.trans ?_
    rw [wt.rest_eq, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    have := blocks_bd (X z) (p z) (ga z) P.r (by omega)
    rw [(hn z).1, (hn z).2] at this
    simpa using this
  · intro z hz q hq
    simp only [blocks, List.mem_cons, List.mem_append, List.mem_map, Finset.mem_toList] at hq
    rcases hq with rfl | rfl | ⟨a, -, rfl⟩ | ⟨x, hx, rfl⟩
    · exact (GlobalTheory.MonBlock.monSupply.2 C V _ _ _ (X z) (F z) 0 _ _).1
    · exact (GlobalTheory.MonBlock.monSupply.2 C V _ _ _ (X z) (F z) 1 _ _).1
    · exact (GlobalTheory.T.characterBlocks_attain_bound.2 C V _ _ _ (X z) (F z) _ a (big_bg _ (alt z hz) a) _).1 (alt z hz)
    · rw [(hn z).1, (hn z).2]
      exact hatt z hz _ _ (Finset.mem_filter.1 hx).2
  · refine le_trans ?_ what₂
    have hc := card_reps P Z hZ
    rw [hP.card] at hc
    have hd : 1 ≤ P.d := Nat.pos_of_ne_zero (NeZero.ne _)
    calc _ ≤ ∑ z ∈ Z, (P.d * (i0 P.k V.l * (P.k - 1)) + 2 * P.r * P.d) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have := blocks_rows (X z) (p z) (ga z) P.r _ hi0 (hlev z hz)
          refine this.trans ?_
          rw [(hn z).1]
          exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hd) _
      _ = _ := by
          rw [Finset.sum_const, smul_eq_mul, ← hc]
          change _ = Z.card * P.d * (i0 P.k V.l * (P.k - 1)) + _
          ring
  · intro z hz g a k
    refine blocks_wt (X z) (alt z hz) (p z) (ga z) P.r ?_ (wt.supp z hz) ?_ g a k
    · have h1 := (hn z).1
      have h2 : (X z).j + (X z).j' = P.m := (hn z).2
      have := hP.r_eq
      omega
    · intro a
      rw [(hn z).1]
      exact wt.main z hz a

end GlobalTheory.PlanValue

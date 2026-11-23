import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeltaCupProduct

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {β κ : Type} [LinearOrder β] [LinearOrder κ]

private theorem lex_cases (t : β ⊕ₗ κ) : (∃ i, t = inlE i) ∨ ∃ l, t = inrE l := by
  obtain ⟨x, rfl⟩ : ∃ x : β ⊕ κ, toLex x = t := ⟨ofLex t, rfl⟩
  rcases x with i | l
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨l, rfl⟩

private theorem mem_uni_l (b : Finset β) (L : Finset κ) (i : β) :
    (inlE i : β ⊕ₗ κ) ∈ uni b L ↔ i ∈ b := by
  simp [uni, inlE]

private theorem mem_uni_r (b : Finset β) (L : Finset κ) (l : κ) :
    (inrE l : β ⊕ₗ κ) ∈ uni b L ↔ l ∈ L := by
  simp [uni, inrE]

private theorem mem_lft (s : Finset (β ⊕ₗ κ)) (i : β) : i ∈ lft s ↔ (inlE i : β ⊕ₗ κ) ∈ s := by
  simp [lft, inlE]

private theorem mem_rgt (s : Finset (β ⊕ₗ κ)) (l : κ) : l ∈ rgt s ↔ (inrE l : β ⊕ₗ κ) ∈ s := by
  simp [rgt, inrE]

private theorem lft_uni (b : Finset β) (L : Finset κ) : lft (uni b L) = b := by
  ext i; rw [mem_lft, mem_uni_l]

private theorem rgt_uni (b : Finset β) (L : Finset κ) : rgt (uni b L) = L := by
  ext l; rw [mem_rgt, mem_uni_r]

private theorem uni_lft_rgt (s : Finset (β ⊕ₗ κ)) : uni (lft s) (rgt s) = s := by
  ext t
  rcases lex_cases t with ⟨i, rfl⟩ | ⟨l, rfl⟩
  · rw [mem_uni_l, mem_lft]
  · rw [mem_uni_r, mem_rgt]

private theorem l_lt_r (i : β) (l : κ) : (inlE i : β ⊕ₗ κ) < inrE l := Sum.Lex.inl_lt_inr i l

private theorem card_uni (b : Finset β) (L : Finset κ) : (uni b L).card = b.card + L.card := by
  simp [uni]

private theorem sum_uni {M : Type} [AddCommMonoid M] (b : Finset β) (L : Finset κ) (f : β ⊕ₗ κ → M) :
    ∑ t ∈ uni b L, f t = ∑ i ∈ b, f (inlE i) + ∑ l ∈ L, f (inrE l) := by
  simp only [uni, Finset.sum_map, Finset.sum_disjSum]
  rfl

private theorem filter_le_l (I : Finset β) (J : Finset κ) (i : β) :
    (uni I J).filter (· ≤ (inlE i : β ⊕ₗ κ)) = uni (I.filter (· ≤ i)) (∅ : Finset κ) := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨l, rfl⟩
  · simp [mem_uni_l]
  · simp [mem_uni_r, not_le.2 (l_lt_r i l)]

private theorem filter_ge_l (I : Finset β) (J : Finset κ) (i : β) :
    (uni I J).filter ((inlE i : β ⊕ₗ κ) ≤ ·) = uni (I.filter (i ≤ ·)) J := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨l, rfl⟩
  · simp [mem_uni_l]
  · simp [mem_uni_r, (l_lt_r i l).le]

private theorem filter_le_r (I : Finset β) (J : Finset κ) (l : κ) :
    (uni I J).filter (· ≤ (inrE l : β ⊕ₗ κ)) = uni I (J.filter (· ≤ l)) := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · simp [mem_uni_l, (l_lt_r j l).le]
  · simp [mem_uni_r]

private theorem filter_ge_r (I : Finset β) (J : Finset κ) (l : κ) :
    (uni I J).filter ((inrE l : β ⊕ₗ κ) ≤ ·) = uni (∅ : Finset β) (J.filter (l ≤ ·)) := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · simp [mem_uni_l, not_le.2 (l_lt_r j l)]
  · simp [mem_uni_r]

private theorem uni_empty : uni (∅ : Finset β) (∅ : Finset κ) = ∅ := by
  ext t
  rcases lex_cases t with ⟨i, rfl⟩ | ⟨l, rfl⟩ <;> simp [mem_uni_l, mem_uni_r]

private def ext0 {X : Type} [Zero X] (x : Finset β → X) : Finset (β ⊕ₗ κ) → X :=
  fun s => if rgt s = ∅ then x (lft s) else 0

end

private theorem card_split {β : Type} [LinearOrder β] (I : Finset β) {i : β} (hi : i ∈ I) :
    (I.filter (· ≤ i)).card + (I.filter (i ≤ ·)).card = I.card + 1 := by
  have h1 : I.filter (· ≤ i) ∪ I.filter (i ≤ ·) = I := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_total x i with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have h2 : I.filter (· ≤ i) ∩ I.filter (i ≤ ·) = {i} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h1⟩, _, h2⟩
      exact le_antisymm h1 h2
    · rintro rfl
      exact ⟨⟨hi, le_rfl⟩, hi, le_rfl⟩
  rw [← Finset.card_union_add_card_inter, h1, h2, Finset.card_singleton]

private theorem wd_one {σ X : Type} [LinearOrder σ] [AddCommGroup X] [Module ℂ X] (c : Finset σ → X) (t : Finset σ) :
    wd (fun _ : σ => (1 : Module.End ℂ X)) c t = GlobalTheory.DI.delta c t := by
  simp [wd, GlobalTheory.DI.delta, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem cech_val {σ X : Type} [LinearOrder σ] [AddCommGroup X] [Module ℂ X] (F : Finset σ → Submodule ℂ X)
    (n : ℕ) {a : Finset σ → X} (h : a ∈ (cech F).Z n) (s : Finset σ) :
    a s = 0 ∨ (s.Nonempty ∧ s.card = n + 1 ∧ a s ∈ F s) := by
  have h1 := (Submodule.mem_pi.1 (Submodule.mem_inf.1 h).1) s (Set.mem_univ _)
  split_ifs at h1 with hc
  · right
    exact ⟨hc.1, by have := hc.2; omega, h1⟩
  · left
    exact (Submodule.mem_bot _).1 h1

private theorem cech_delta {σ X : Type} [LinearOrder σ] [AddCommGroup X] [Module ℂ X] (F : Finset σ → Submodule ℂ X)
    (n : ℕ) {a : Finset σ → X} (h : a ∈ (cech F).Z n) : GlobalTheory.DI.delta a = 0 :=
  LinearMap.mem_ker.1 (Submodule.mem_inf.1 h).2

private theorem delta_cupE {σ E E' E'' : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup E''] [Module ℂ E''] (μ : E →ₗ[ℂ] E' →ₗ[ℂ] E'') (a : Finset σ → E) (b : Finset σ → E')
    (ha : a ∅ = 0) (hb : b ∅ = 0) (hd : GlobalTheory.DI.delta b = 0) (u : Finset σ) :
    GlobalTheory.DI.delta (cupE μ a b) u = cupE μ (GlobalTheory.DI.delta a) b u := by
  let Φ : E × E'' →+ (Finset σ → E × E'') :=
    { toFun := fun x t => ((0 : E), μ x.1 (b t))
      map_zero' := by
        funext t
        simp
      map_add' := by
        intro x y
        funext t
        refine Prod.ext ?_ ?_ <;> simp }
  let c : Finset σ → E × E'' := fun t => (a t, 0)
  have key := GlobalTheory.DI.delta_cup_eq Φ c
    (fun x => by
      show ((0 : E), μ x.1 (b ∅)) = 0
      simp [hb])
    (by
      show (a ∅, (0 : E'')) = 0
      simp [ha]) u
  have hsnd : ∀ (f : Finset σ → E × E'') (t : Finset σ),
      (GlobalTheory.DI.delta f t).2 = GlobalTheory.DI.delta (fun s => (f s).2) t := by
    intro f t
    simp [GlobalTheory.DI.delta, Prod.snd_sum]
  have hfst : ∀ (f : Finset σ → E × E'') (t : Finset σ),
      (GlobalTheory.DI.delta f t).1 = GlobalTheory.DI.delta (fun s => (f s).1) t := by
    intro f t
    simp [GlobalTheory.DI.delta, Prod.fst_sum]
  have h1 : (fun t => (GlobalTheory.DI.cup Φ c t).2) = cupE μ a b := by
    funext t
    simp only [GlobalTheory.DI.cup, cupE, Prod.snd_sum]
    rfl
  have h3 : (GlobalTheory.DI.cup Φ (GlobalTheory.DI.delta c) u).2 = cupE μ (GlobalTheory.DI.delta a) b u := by
    simp only [GlobalTheory.DI.cup, cupE, Prod.snd_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show μ (GlobalTheory.DI.delta c _).1 _ = _
    rw [hfst]
  have h5 : ∀ (x : E × E'') (t : Finset σ), GlobalTheory.DI.delta (fun s => (Φ x s).2) t = 0 := by
    intro x t
    show GlobalTheory.DI.delta (fun s => μ x.1 (b s)) t = 0
    have : GlobalTheory.DI.delta (fun s => μ x.1 (b s)) t = μ x.1 (GlobalTheory.DI.delta b t) := by
      simp [GlobalTheory.DI.delta, map_sum, map_zsmul]
    rw [this, hd]
    simp
  have h4 : ∀ j ∈ u, ((-1 : ℤ) ^ (u.filter (· < j)).card •
      GlobalTheory.DI.delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·))).2 = 0 := by
    intro j _
    rw [Prod.smul_snd, hsnd, h5, smul_zero]
  calc GlobalTheory.DI.delta (cupE μ a b) u = (GlobalTheory.DI.delta (GlobalTheory.DI.cup Φ c) u).2 := by
        rw [hsnd, h1]
    _ = _ := by
        rw [key, Prod.snd_add, h3, Prod.snd_sum, Finset.sum_eq_zero h4, add_zero]

section
variable {β κ : Type} [LinearOrder β] [LinearOrder κ]

private theorem delta_ext (hU : WdUni) {X : Type} [AddCommGroup X] [Module ℂ X] (x : Finset β → X)
    (hx : GlobalTheory.DI.delta x = 0) (I : Finset β) (J : Finset κ) :
    GlobalTheory.DI.delta (ext0 (κ := κ) x) (uni I J) = ((-1 : ℤ) ^ I.card) • edge1 (κ := κ) x (uni I J) := by
  have hs : ∀ (y : X) (L : Finset κ),
      GlobalTheory.DI.delta (fun L' : Finset κ => if L' = ∅ then y else 0) L = if L.card = 1 then y else 0 := by
    intro y L
    by_cases h : L.card = 1
    · obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h
      simp [GlobalTheory.DI.delta, GlobalTheory.cubeSign_singleton]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro l hl
      have hne : L.erase l ≠ ∅ := by
        intro he
        rcases (Finset.erase_eq_empty_iff L l).1 he with h0 | h0
        · rw [h0] at hl
          simp at hl
        · exact h (by rw [h0, Finset.card_singleton])
      show GlobalTheory.cubeSign L l • (if L.erase l = ∅ then y else 0) = 0
      rw [if_neg hne, smul_zero]
  have key := (hU β κ X (fun _ => 1) (ext0 x) I J).1
  simp only [wd_one] at key
  rw [key]
  have e1 : (fun b' => ext0 (κ := κ) x (uni b' J)) = fun b' => if J = ∅ then x b' else 0 := by
    funext b'
    simp [ext0, lft_uni, rgt_uni]
  have e2 : (fun L' => ext0 (κ := κ) x (uni I L')) = fun L' => if L' = ∅ then x I else 0 := by
    funext L'
    simp [ext0, lft_uni, rgt_uni]
  rw [e1, e2, hs]
  have e3 : GlobalTheory.DI.delta (fun b' => if J = ∅ then x b' else 0) I = 0 := by
    by_cases hJ : J = ∅
    · simp only [if_pos hJ]
      exact congrFun hx I
    · simp [hJ, GlobalTheory.DI.delta]
  rw [e3, zero_add]
  simp [edge1, lft_uni, rgt_uni]

variable {E E' E'' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  [AddCommGroup E''] [Module ℂ E''] (μ : E →ₗ[ℂ] E' →ₗ[ℂ] E'')

private theorem cup_ext_uni (a : Finset β → E) (c : Finset (β ⊕ₗ κ) → E') (I : Finset β) (J : Finset κ) :
    cupE μ (ext0 a) c (uni I J) =
      ∑ i ∈ I, μ (a (I.filter (· ≤ i))) (c (uni (I.filter (i ≤ ·)) J)) := by
  simp only [cupE]
  rw [sum_uni]
  beta_reduce
  rw [Finset.sum_eq_zero (s := J) (fun l hl => ?_), add_zero]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [filter_le_l, filter_ge_l, ext0, lft_uni, rgt_uni]
  · have hne : J.filter (· ≤ l) ≠ ∅ := by
      intro he
      have hm : l ∈ J.filter (· ≤ l) := Finset.mem_filter.2 ⟨hl, le_rfl⟩
      rw [he] at hm
      simp at hm
    simp only [filter_le_r, ext0, rgt_uni, if_neg hne, map_zero, LinearMap.zero_apply]

private theorem cup_edge (q : ℕ) (a : Finset β → E) (ha : ∀ I : Finset β, I.card ≠ q + 1 → a I = 0)
    (c : Finset (β ⊕ₗ κ) → E') (hc : c ∅ = 0) (I : Finset β) (J : Finset κ) :
    cupE μ (fun v => ((-1 : ℤ) ^ (lft v).card) • edge1 (κ := κ) a v) c (uni I J) =
      ((-1 : ℤ) ^ (q + 1)) • join μ a (fun J => c (uni ∅ J)) (uni I J) := by
  simp only [cupE]
  rw [sum_uni]
  beta_reduce
  rw [Finset.sum_eq_zero (s := I) (fun i _ => ?_), zero_add]
  · simp only [join, lft_uni, rgt_uni]
    rcases J.eq_empty_or_nonempty with hJ | hJ
    · subst hJ
      simp [uni_empty, hc]
    · rw [Finset.sum_eq_single_of_mem (J.min' hJ) (J.min'_mem hJ) (fun l hl hne => ?_)]
      · have e1 : J.filter (· ≤ J.min' hJ) = {J.min' hJ} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx, h⟩
            exact le_antisymm h (J.min'_le x hx)
          · rintro rfl
            exact ⟨J.min'_mem hJ, le_rfl⟩
        have e2 : J.filter (J.min' hJ ≤ ·) = J :=
          Finset.filter_true_of_mem (fun x hx => J.min'_le x hx)
        simp only [filter_le_r, filter_ge_r, e1, e2, edge1, lft_uni, rgt_uni, Finset.card_singleton,
          if_pos rfl, map_zsmul, LinearMap.smul_apply, if_true]
        by_cases hI : I.card = q + 1
        · rw [hI]
        · rw [ha I hI]
          simp
      · have h2 : 1 < (J.filter (· ≤ l)).card :=
          Finset.one_lt_card.2 ⟨J.min' hJ, Finset.mem_filter.2 ⟨J.min'_mem hJ, J.min'_le l hl⟩,
            l, Finset.mem_filter.2 ⟨hl, le_rfl⟩, Ne.symm hne⟩
        simp only [filter_le_r, edge1, lft_uni, rgt_uni, if_neg h2.ne', smul_zero, map_zero,
          LinearMap.zero_apply]
  · simp [filter_le_l, edge1, rgt_uni]

end

theorem UpperTheory.Gal.productCup_of_system.lCupRel_of :
    WdUni → LCupRel := by
  intro hU ι _ _ E E' E'' _ _ _ _ _ _ μ A G H q p hH a ha γ hγ
  have ha0 : a ∅ = 0 := by
    rcases cech_val A q ha ∅ with h | ⟨h, _⟩
    · exact h
    · exact absurd h (by simp)
  have hγ0 : γ ∅ = 0 := by
    rcases cech_val G p hγ ∅ with h | ⟨h, _⟩
    · exact h
    · exact absurd h (by simp)
  have hda : GlobalTheory.DI.delta a = 0 := cech_delta A q ha
  have hdγ : GlobalTheory.DI.delta γ = 0 := cech_delta G p hγ
  have haq : ∀ I : Finset ι, I.card ≠ q + 1 → a I = 0 := by
    intro I hI
    rcases cech_val A q ha I with h | ⟨_, h, _⟩
    · exact h
    · exact absurd h hI
  have hempty : ∀ f : Finset ι → E', GlobalTheory.DI.delta f ∅ = 0 := fun f => by simp [GlobalTheory.DI.delta]
  set wL : Finset ι → E' := fun I => γ (uni I ∅) with hwL
  set w : Finset ι → E'' := cupE μ a wL with hw
  have hdwL : GlobalTheory.DI.delta wL = 0 := by
    funext I
    have key := (hU ι ι E' (fun _ => 1) γ I ∅).1
    simp only [wd_one] at key
    rw [hdγ, hempty, smul_zero, add_zero, Pi.zero_apply] at key
    exact key.symm
  have hdw : GlobalTheory.DI.delta w = 0 := by
    funext u
    have hwL0 : wL ∅ = 0 := by
      show γ (uni ∅ ∅) = 0
      rw [uni_empty, hγ0]
    rw [hw, delta_cupE μ a wL ha0 hwL0 hdwL u, hda]
    simp [cupE]
  have hcard : ∀ (I J : Finset ι) (i : ι), i ∈ I → I.card + J.card ≠ q + p + 1 →
      μ (a (I.filter (· ≤ i))) (γ (uni (I.filter (i ≤ ·)) J)) = 0 := by
    intro I J i hi hne
    rcases cech_val A q ha (I.filter (· ≤ i)) with h0 | ⟨_, h1, _⟩
    · rw [h0]
      simp
    rcases cech_val G p hγ (uni (I.filter (i ≤ ·)) J) with h0 | ⟨_, h2, _⟩
    · rw [h0]
      simp
    exfalso
    apply hne
    rw [card_uni] at h2
    have := card_split I hi
    omega
  have hwcard : ∀ I : Finset ι, I.card ≠ q + p + 1 → w I = 0 := by
    intro I hI
    rw [hw]
    simp only [cupE]
    apply Finset.sum_eq_zero
    intro i hi
    exact hcard I ∅ i hi (by simpa using hI)
  have hext_a : ext0 (κ := ι) a ∅ = 0 := by
    rw [← uni_empty (β := ι) (κ := ι)]
    show (if rgt (uni (∅ : Finset ι) (∅ : Finset ι)) = ∅ then a (lft (uni ∅ ∅)) else 0) = 0
    rw [rgt_uni, lft_uni, if_pos rfl, ha0]
  have hdext_a : GlobalTheory.DI.delta (ext0 (κ := ι) a) =
      fun v => ((-1 : ℤ) ^ (lft v).card) • edge1 (κ := ι) a v := by
    funext v
    rw [← uni_lft_rgt v, delta_ext hU a hda, lft_uni]
  have hsub : ∀ (f g : Finset (ι ⊕ₗ ι) → E'') t,
      GlobalTheory.DI.delta (f - g) t = GlobalTheory.DI.delta f t - GlobalTheory.DI.delta g t := by
    intro f g t
    simp [GlobalTheory.DI.delta, Finset.sum_sub_distrib, smul_sub]
  have hdY : ∀ v, GlobalTheory.DI.delta (cupE μ (ext0 (κ := ι) a) γ - ext0 (κ := ι) w) v =
      (-1 : ℤ) ^ (q + 1) • ((join μ a fun J => γ (uni ∅ J)) - (-1 : ℤ) ^ p • edge1 (κ := ι) w) v := by
    intro v
    obtain ⟨I, J, rfl⟩ : ∃ I J, v = uni I J := ⟨lft v, rgt v, (uni_lft_rgt v).symm⟩
    rw [hsub, delta_cupE μ _ γ hext_a hγ0 hdγ, hdext_a, cup_edge μ q a haq γ hγ0 I J,
      delta_ext hU w hdw I J, Pi.sub_apply, Pi.smul_apply, smul_sub, smul_smul]
    congr 1
    by_cases hI : I.card = q + p + 1
    · rw [hI, ← pow_add, show q + 1 + p = q + p + 1 by omega]
    · simp [edge1, lft_uni, rgt_uni, hwcard I hI]
  have hsubuni : ∀ (I J : Finset ι) (i : ι), uni (I.filter (i ≤ ·)) J ⊆ uni I J := by
    intro I J i t ht
    rcases lex_cases t with ⟨j, rfl⟩ | ⟨l, rfl⟩
    · rw [mem_uni_l] at ht ⊢
      exact (Finset.mem_filter.1 ht).1
    · rw [mem_uni_r] at ht ⊢
      exact ht
  have hYmem : ∀ s : Finset (ι ⊕ₗ ι), (cupE μ (ext0 (κ := ι) a) γ - ext0 (κ := ι) w) s ∈
      (if (s.card : ℤ) = (q : ℤ) + p + 2 - 1 then mixF H s else ⊥) := by
    intro s
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [Pi.sub_apply, cup_ext_uni]
    rcases J.eq_empty_or_nonempty with hJ | hJ
    · subst hJ
      have e : ext0 (κ := ι) w (uni I ∅) =
          ∑ i ∈ I, μ (a (I.filter (· ≤ i))) (γ (uni (I.filter (i ≤ ·)) ∅)) := by
        show (if rgt (uni I (∅ : Finset ι)) = ∅ then w (lft (uni I ∅)) else 0) = _
        rw [rgt_uni, lft_uni, if_pos rfl, hw]
        rfl
      rw [e, sub_self]
      exact Submodule.zero_mem _
    · have h0 : ext0 (κ := ι) w (uni I J) = 0 := by
        show (if rgt (uni I J) = ∅ then w (lft (uni I J)) else 0) = 0
        rw [rgt_uni, if_neg hJ.ne_empty]
      rw [h0, sub_zero]
      split_ifs with hc
      · rcases I.eq_empty_or_nonempty with hI | hI
        · subst hI
          simp
        · rw [show mixF H (uni I J) = H I J by simp [mixF, lft_uni, rgt_uni, hI, hJ]]
          apply Submodule.sum_mem
          intro i _
          rcases cech_val A q ha (I.filter (· ≤ i)) with h0 | ⟨hne, _, hmem⟩
          · rw [h0, map_zero, LinearMap.zero_apply]
            exact Submodule.zero_mem _
          rcases cech_val G p hγ (uni (I.filter (i ≤ ·)) J) with h0 | ⟨hne', _, hmem'⟩
          · rw [h0, map_zero]
            exact Submodule.zero_mem _
          exact hH I J _ _ hJ hne hne' (Finset.filter_subset _ _) (hsubuni I J i) _ hmem _ hmem'
      · rw [Finset.sum_eq_zero (fun i hi => hcard I J i hi (fun h => hc (by
          rw [card_uni]
          push_cast
          omega)))]
        exact Submodule.zero_mem _
  refine ⟨?_, ?_⟩
  · refine Submodule.mem_map.2 ⟨(-1 : ℤ) ^ (q + 1) • (cupE μ (ext0 (κ := ι) a) γ - ext0 (κ := ι) w),
      zsmul_mem (Submodule.mem_pi.2 (fun s _ => hYmem s)) _, ?_⟩
    show wd (fun _ => (1 : Module.End ℂ E''))
      ((-1 : ℤ) ^ (q + 1) • (cupE μ (ext0 (κ := ι) a) γ - ext0 (κ := ι) w)) = _
    rw [map_zsmul]
    funext v
    rw [Pi.smul_apply, wd_one, hdY v, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  · exact hdw

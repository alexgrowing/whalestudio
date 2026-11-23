import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section SlopeTestRemainingChoices

private lemma mem_lft' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (s : Finset (ι ⊕ₗ κ)) (a : ι) :
    a ∈ lft s ↔ toLex (Sum.inl a) ∈ s := by
  simp [lft, Finset.mem_toLeft]

private lemma mem_rgt' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (s : Finset (ι ⊕ₗ κ)) (a : κ) :
    a ∈ rgt s ↔ toLex (Sum.inr a) ∈ s := by
  simp [rgt, Finset.mem_toRight]

private lemma lft_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s s' : Finset (ι ⊕ₗ κ)} (h : s ⊆ s') :
    lft s ⊆ lft s' := fun a ha => (mem_lft' _ _).2 (h ((mem_lft' _ _).1 ha))

private lemma rgt_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s s' : Finset (ι ⊕ₗ κ)} (h : s ⊆ s') :
    rgt s ⊆ rgt s' := fun a ha => (mem_rgt' _ _).2 (h ((mem_rgt' _ _).1 ha))

private lemma pk_mem' {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  unfold pk
  rw [dif_pos h]
  exact Finset.min'_mem _ _

variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  {κ : Type} [LinearOrder κ]

private lemma u_quot (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (l : κ) :
    ((T.u n a b l * (T.u n a' b' l)⁻¹ : Sˣ) : S) ∈ T.R I J := by
  have e : T.u n a b l * (T.u n a' b' l)⁻¹ =
      (T.X a * (T.X a')⁻¹) ^ (n l).1 * (T.Y b * (T.Y b')⁻¹) ^ (n l).2 := by
    simp only [Sys.u, mul_inv, mul_pow, inv_pow]
    ac_rfl
  rw [e, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact mul_mem (pow_mem (hT.memX I J hJ a' ha' a) _) (pow_mem (hT.memY I J hI b' hb' b) _)

private lemma prod_quot (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (L : Finset κ) :
    (((∏ l ∈ L, T.u n a b l) * (∏ l ∈ L, T.u n a' b' l)⁻¹ : Sˣ) : S) ∈ T.R I J := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
  exact Subalgebra.prod_mem _ (fun l _ => u_quot T hT n hI hJ ha' hb' l)

private lemma lat_le (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha' : a' ∈ I) (hb' : b' ∈ J) (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n a b l : Sˣ) : S)) ≤
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n a' b' l : Sˣ) : S)) := by
  rintro y ⟨m, hm, rfl⟩
  have hr := prod_quot T hT n hI hJ (a := a) (b := b) ha' hb' L
  refine ⟨T.act (((∏ l ∈ L, T.u n a b l) * (∏ l ∈ L, T.u n a' b' l)⁻¹ : Sˣ) : S) m,
    hT.stab I J hI hJ _ hr m hm, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul, ← Units.val_mul, mul_comm (∏ l ∈ L, T.u n a b l),
    mul_inv_cancel_left]

private lemma lat_eq (hT : T.Good) (n : κ → ℕ × ℕ) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {a a' b b' : Fin (d + 1)} (ha : a ∈ I) (ha' : a' ∈ I) (hb : b ∈ J) (hb' : b' ∈ J) (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n a b l : Sˣ) : S)) =
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n a' b' l : Sˣ) : S)) :=
  le_antisymm (lat_le T hT n hI hJ ha' hb' L) (lat_le T hT n hI hJ ha hb L)

private lemma lat_mono (hT : T.Good) (n : κ → ℕ × ℕ) {I I' J J' : Finset (Fin (d + 1))} (hI : I.Nonempty)
    (hJ : J.Nonempty) (hII : I ⊆ I') (hJJ : J ⊆ J') (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) ≤
      (T.M I' J').map (T.act ((∏ l ∈ L, T.u n (pk I') (pk J') l : Sˣ) : S)) := by
  have hI' := Finset.Nonempty.mono hII hI
  have hJ' := Finset.Nonempty.mono hJJ hJ
  calc (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))
      ≤ (T.M I' J').map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) :=
        Submodule.map_mono (hT.monoM I I' J J' hI hJ hII hJJ)
    _ = _ := lat_eq T hT n hI' hJ' (hII (pk_mem' hI)) (pk_mem' hI') (hJJ (pk_mem' hJ)) (pk_mem' hJ') L

private lemma r_mem (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) (hA : T.admitted n z) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) (l : κ) : T.r n z i j l ∈ T.R I J :=
  hT.monoR {i} I {j} J (Finset.singleton_nonempty i) (Finset.singleton_nonempty j)
    (Finset.singleton_subset_iff.2 hi) (Finset.singleton_subset_iff.2 hj) (hA i j l)

private lemma col_eq (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    T.colCx n z I J = kosT T.act (T.M I J) (T.u n i j) z := by
  unfold Sys.colCx kosT
  congr 1
  funext L
  exact lat_eq T hT n ⟨i, hi⟩ ⟨j, hj⟩ (pk_mem' ⟨i, hi⟩) hi (pk_mem' ⟨j, hj⟩) hj L

private lemma mix_mono (hT : T.Good) (n : κ → ℕ × ℕ) (L : Finset κ) {s s' : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1))}
    (hs : s ⊆ s') {m : E}
    (hm : m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s) :
    m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s' := by
  unfold mixF at hm ⊢
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · have h' : (lft s').Nonempty ∧ (rgt s').Nonempty :=
      ⟨Finset.Nonempty.mono (lft_mono' hs) h.1, Finset.Nonempty.mono (rgt_mono' hs) h.2⟩
    rw [if_pos h] at hm
    rw [if_pos h']
    exact lat_mono T hT n h.1 h.2 (lft_mono' hs) (rgt_mono' hs) L hm
  · rw [if_neg h, Submodule.mem_bot] at hm
    subst hm
    exact zero_mem _

private lemma mix_step (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S) (hA : T.admitted n z) (L : Finset κ) {l : κ} (hl : l ∉ L)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1))) {m : E}
    (hm : m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S))) s) :
    T.act (z l) m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ insert l L, T.u n (pk I) (pk J) l : Sˣ) : S))) s := by
  unfold mixF at hm ⊢
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · rw [if_pos h] at hm ⊢
    rw [Submodule.mem_map] at hm ⊢
    obtain ⟨m0, hm0, rfl⟩ := hm
    refine ⟨T.act (T.r n z (pk (lft s)) (pk (rgt s)) l) m0,
      hT.stab _ _ h.1 h.2 _ (r_mem T hT n z hA (pk_mem' h.1) (pk_mem' h.2) l) m0 hm0, ?_⟩
    have e : ((∏ k ∈ insert l L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S) *
        T.r n z (pk (lft s)) (pk (rgt s)) l =
        z l * ((∏ k ∈ L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S) := by
      have hu := Units.mul_inv (T.u n (pk (lft s)) (pk (rgt s)) l)
      rw [Finset.prod_insert hl, Units.val_mul]
      simp only [Sys.r]
      linear_combination (z l * ((∏ k ∈ L, T.u n (pk (lft s)) (pk (rgt s)) k : Sˣ) : S)) * hu
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
  · rw [if_neg h, Submodule.mem_bot] at hm
    rw [if_neg h, hm, map_zero]
    exact zero_mem _

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.productCup_of_system.sysOk_of :
    WdUni → SysOk := by
  intro _
  unfold SysOk
  intro d S E _ _ _ _ T κ _ _ n z hT hA
  refine ⟨⟨?_, ?_⟩, fun I J i hi j hj => ⟨fun l => r_mem T hT n z hA hi hj l, col_eq T hT n z hi hj⟩, ?_⟩
  · intro i j
    unfold Sys.wt
    rcases ofLex i with a | a <;> rcases ofLex j with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact Commute.one_left _
    · exact Commute.one_left _
    · exact Commute.one_right _
    · exact (Commute.all (z a) (z b)).map T.act
  · intro s t ht m hm
    obtain ⟨x, rfl⟩ : ∃ x : Two d ⊕ κ, toLex x = t := ⟨ofLex t, rfl⟩
    beta_reduce at hm ⊢
    rcases x with a | l
    · have hw : T.wt z (toLex (Sum.inl a)) = 1 := rfl
      rw [hw, Module.End.one_apply]
      have gen : ∀ s1 : Finset (Two d ⊕ₗ κ), lft s ⊆ lft s1 → rgt s1 = rgt s →
          m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s1, T.u n (pk I) (pk J) l : Sˣ) : S)))
            (lft s1) := by
        intro s1 h1 h2
        rw [h2]
        exact mix_mono T hT n (rgt s) h1 hm
      refine gen _ ?_ ?_
      · intro b hb
        rw [mem_lft'] at hb ⊢
        simp [hb]
      · ext b
        simp [mem_rgt']
    · have hl : l ∉ rgt s := fun h => ht ((mem_rgt' s l).1 h)
      have key := mix_step T hT n z hA (rgt s) hl (lft s) hm
      have hw : T.wt z (toLex (Sum.inr l)) = T.act (z l) := rfl
      rw [hw]
      have gen : ∀ s1 : Finset (Two d ⊕ₗ κ), lft s1 = lft s → rgt s1 = insert l (rgt s) →
          T.act (z l) m ∈ mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s1, T.u n (pk I) (pk J) l : Sˣ) : S)))
            (lft s1) := by
        intro s1 h1 h2
        rw [h1, h2]
        exact key
      refine gen _ ?_ ?_
      · ext b
        simp [mem_lft']
      · ext b
        simp [mem_rgt']
  · intro I I' J J' hI hJ hII hJJ m x hx
    simp only [Cx.Z, Sys.colCx, kosT, acx, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ,
      true_implies] at hx ⊢
    refine ⟨fun L => ?_, hx.2⟩
    have hxL := hx.1 L
    split_ifs at hxL ⊢
    · exact lat_mono T hT n hI hJ hII hJJ L hxL
    · exact hxL

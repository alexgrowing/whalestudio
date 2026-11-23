import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.ChainInd

section Abstract

variable {V : Type} [Fintype V] [DecidableEq V]

theorem exists_least (R : V → V → Prop) (hr : ∀ x, R x x) (ht : ∀ x y z, R x y → R y z → R x z)
    (B : Finset V) (hne : B.Nonempty) (hc : IsChain R (↑B : Set V)) : ∃ e ∈ B, ∀ x ∈ B, R e x := by
  revert hne hc
  refine Finset.induction_on B ?_ ?_
  · intro hne _
    exact absurd hne Finset.not_nonempty_empty
  · intro a s ha ih hne hc
    have hcs : IsChain R (↑s : Set V) := hc.mono (Finset.coe_subset.2 (Finset.subset_insert a s))
    by_cases hs : s.Nonempty
    · obtain ⟨e, he, hle⟩ := ih hs hcs
      have hae : a ≠ e := fun h => ha (h ▸ he)
      rcases hc (Finset.mem_coe.2 (Finset.mem_insert_self a s))
          (Finset.mem_coe.2 (Finset.mem_insert_of_mem he)) hae with h | h
      · refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hr _
        · exact ht _ _ _ h (hle x hx)
      · refine ⟨e, Finset.mem_insert_of_mem he, fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact h
        · exact hle x hx
    · refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hr _
      · exact absurd ⟨x, hx⟩ hs

theorem sum_chains_eq_zero (R : V → V → Prop) (hr : ∀ x, R x x) (ht : ∀ x y z, R x y → R y z → R x z)
    (A : V → Prop) (es : V) (hes : A es) (mt : V → V) (h1 : ∀ e, R (mt e) e) (h2 : ∀ e, R (mt e) es)
    (h3 : ∀ x e, R x e → R x es → R x (mt e)) (h4 : ∀ e, A e → A (mt e))
    [DecidablePred fun s : Finset V => IsChain R (↑s : Set V) ∧ ∀ e ∈ s, A e] :
    ∑ s ∈ (Finset.univ : Finset (Finset V)).filter
      (fun s : Finset V => IsChain R (↑s : Set V) ∧ ∀ e ∈ s, A e), (-1 : ℝ) ^ s.card = 0 := by
  classical
  obtain ⟨least, hleast⟩ : ∃ least : Finset V → V, ∀ U : Finset V, U.Nonempty → IsChain R (↑U : Set V) →
      least U ∈ U ∧ ∀ x ∈ U, R (least U) x :=
    ⟨fun U => if h : U.Nonempty ∧ IsChain R (↑U : Set V) then
        Classical.choose (exists_least R hr ht U h.1 h.2) else es,
      fun U hU hcU => by
        beta_reduce
        rw [dif_pos ⟨hU, hcU⟩]
        exact Classical.choose_spec (exists_least R hr ht U hU hcU)⟩
  obtain ⟨U, hU⟩ : ∃ U : Finset V → Finset V, ∀ s, U s = s.filter (fun x => ¬ R x es) :=
    ⟨_, fun _ => rfl⟩
  have hmem : ∀ s x, x ∈ U s ↔ x ∈ s ∧ ¬ R x es := fun s x => by rw [hU, Finset.mem_filter]
  obtain ⟨c, hc⟩ : ∃ c : Finset V → V, ∀ s, c s = if (U s).Nonempty then mt (least (U s)) else es :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Finset V → Finset V, ∀ s, g s = if c s ∈ s then s.erase (c s) else insert (c s) s :=
    ⟨_, fun _ => rfl⟩
  have hcD : ∀ s, R (c s) es := by
    intro s
    rw [hc]
    split_ifs
    · exact h2 _
    · exact hr es
  have hUg : ∀ s, U (g s) = U s := by
    intro s
    rw [hU, hU, hg]
    split_ifs with h
    · ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hx⟩, hxR⟩
        exact ⟨hx, hxR⟩
      · rintro ⟨hx, hxR⟩
        refine ⟨⟨?_, hx⟩, hxR⟩
        rintro rfl
        exact hxR (hcD s)
    · ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxR⟩
        · exact absurd (hcD s) hxR
        · exact ⟨hx, hxR⟩
      · rintro ⟨hx, hxR⟩
        exact ⟨Or.inr hx, hxR⟩
  have hcg : ∀ s, c (g s) = c s := by
    intro s
    rw [hc, hc, hUg]
  have hgg : ∀ s, g (g s) = s := by
    intro s
    by_cases h : c s ∈ s
    · have e1 : g s = s.erase (c s) := by rw [hg, if_pos h]
      have e2 : c s ∉ g s := by rw [e1]; simp
      rw [hg (g s), hcg, if_neg e2, e1, Finset.insert_erase h]
    · have e1 : g s = insert (c s) s := by rw [hg, if_neg h]
      have e2 : c s ∈ g s := by rw [e1]; exact Finset.mem_insert_self (c s) s
      rw [hg (g s), hcg, if_pos e2, e1, Finset.erase_insert h]
  refine Finset.sum_involution (fun s _ => g s) ?_ ?_ ?_ ?_
  · intro s _
    by_cases h : c s ∈ s
    · have e1 : g s = s.erase (c s) := by rw [hg, if_pos h]
      rw [← Finset.card_erase_add_one h, ← e1, pow_succ]
      ring
    · have e1 : g s = insert (c s) s := by rw [hg, if_neg h]
      rw [e1, Finset.card_insert_eq_ite, if_neg h, pow_succ]
      ring
  · intro s _ _ hEq
    by_cases h : c s ∈ s
    · have e1 : g s = s.erase (c s) := by rw [hg, if_pos h]
      have e2 : c s ∉ g s := by rw [e1]; simp
      rw [hEq] at e2
      exact e2 h
    · have e1 : g s = insert (c s) s := by rw [hg, if_neg h]
      have e2 : c s ∈ g s := by rw [e1]; exact Finset.mem_insert_self (c s) s
      rw [hEq] at e2
      exact h e2
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨_, hcs, hA⟩ := hs
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases h : c s ∈ s
    · have e1 : g s = s.erase (c s) := by rw [hg, if_pos h]
      rw [e1]
      exact ⟨hcs.mono (Finset.coe_subset.2 (Finset.erase_subset _ _)),
        fun e he => hA e (Finset.mem_of_mem_erase he)⟩
    · have e1 : g s = insert (c s) s := by rw [hg, if_neg h]
      have hUc : ∀ hne : (U s).Nonempty, least (U s) ∈ U s ∧ ∀ x ∈ U s, R (least (U s)) x := fun hne =>
        hleast (U s) hne (hcs.mono (by rw [hU]; exact Finset.coe_subset.2 (Finset.filter_subset _ _)))
      rw [e1]
      refine ⟨?_, ?_⟩
      · rw [Finset.coe_insert]
        refine hcs.insert fun x hx _ => ?_
        have hx' : x ∈ s := Finset.mem_coe.1 hx
        rw [hc]
        split_ifs with hne
        · obtain ⟨hu, hul⟩ := hUc hne
          have hu' := (hmem s _).1 hu
          by_cases hxR : R x es
          · right
            have hxu : x ≠ least (U s) := fun hE => hu'.2 (hE ▸ hxR)
            rcases hcs (Finset.mem_coe.2 hx') (Finset.mem_coe.2 hu'.1) hxu with h5 | h5
            · exact h3 x _ h5 hxR
            · exact absurd (ht _ _ _ h5 hxR) hu'.2
          · left
            have hxU : x ∈ U s := (hmem s x).2 ⟨hx', hxR⟩
            exact ht _ _ _ (h1 _) (hul x hxU)
        · right
          by_contra hxR
          exact hne ⟨x, (hmem s x).2 ⟨hx', hxR⟩⟩
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · rw [hc]
          split_ifs with hne
          · obtain ⟨hu, _⟩ := hUc hne
            exact h4 _ (hA _ ((hmem s _).1 hu).1)
          · exact hes
        · exact hA e he
  · intro s _
    exact hgg s

end Abstract

section Signs

variable {m : ℕ}

theorem sLe_refl (e : Fin m → SignType) : SLe e e := by
  intro i _
  rfl

theorem sLe_trans (a b c : Fin m → SignType) (h : SLe a b) (h' : SLe b c) : SLe a c := by
  intro i hi
  have hb : b i = a i := h i hi
  rw [h' i (by rw [hb]; exact hi), hb]

theorem sMeet_le_left (e e' : Fin m → SignType) : SLe (sMeet e e') e := by
  intro i hi
  simp only [sMeet] at hi ⊢
  by_cases h : e i = e' i
  · rw [if_pos h]
  · rw [if_neg h] at hi
    exact absurd rfl hi

theorem sMeet_le_right (e e' : Fin m → SignType) : SLe (sMeet e e') e' := by
  intro i hi
  simp only [sMeet] at hi ⊢
  by_cases h : e i = e' i
  · rw [if_pos h, h]
  · rw [if_neg h] at hi
    exact absurd rfl hi

theorem le_sMeet (x e e' : Fin m → SignType) (h : SLe x e) (h' : SLe x e') : SLe x (sMeet e e') := by
  intro i hi
  simp only [sMeet]
  have h1 : e i = x i := h i hi
  have h2 : e' i = x i := h' i hi
  rw [if_pos (h1.trans h2.symm), h1]

theorem sdot_zero (a : Fin m → ℝ) : sdot (0 : Fin m → SignType) a = 0 := by simp [sdot]

theorem sdot_meet_join (e e' : Fin m → SignType) (a : Fin m → ℝ) :
    sdot e a + sdot e' a = sdot (sMeet e e') a + sdot (sJoin e e') a := by
  simp only [sdot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sMeet, sJoin]
  cases h1 : e i <;> cases h2 : e' i <;> simp <;> ring

open Classical in

theorem gam_eq_sum (y : (Fin m → SignType) → ℝ) (a : Fin m → ℝ) (h0 : ¬ y 0 < sdot 0 a) :
    gam y a = ∑ s ∈ (Finset.univ : Finset (Finset (Fin m → SignType))).filter
      (fun s : Finset (Fin m → SignType) =>
        IsChain SLe (↑s : Set (Fin m → SignType)) ∧ ∀ e ∈ s, y e < sdot e a), (-1 : ℝ) ^ s.card := by
  simp only [gam, gamOn]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_boole]
  by_cases hA : ∀ e ∈ s, y e < sdot e a
  · by_cases hc : IsChain SLe (↑s : Set (Fin m → SignType))
    · have h0s : (0 : Fin m → SignType) ∉ s := fun h => h0 (hA 0 h)
      simp [hA, hc, h0s]
    · simp [hA, hc]
  · simp [hA]

theorem gam_eq_indicator : ∀ m : ℕ, ∀ (y : (Fin m → SignType) → ℝ) a, PosFam y →
    gam y a = Set.indicator {a | ∀ e, sdot e a ≤ y e} 1 a := by
  intro m y a hy
  classical
  have hy' : y 0 = 0 ∧ ∀ e e', y (sMeet e e') + y (sJoin e e') ≤ y e + y e' := hy
  have h0 : ¬ y 0 < sdot 0 a := by
    rw [hy'.1, sdot_zero]
    exact lt_irrefl 0
  rw [gam_eq_sum y a h0]
  by_cases hall : ∀ e, sdot e a ≤ y e
  · rw [Set.indicator_of_mem (show a ∈ {a | ∀ e, sdot e a ≤ y e} from hall)]
    refine (Finset.sum_eq_single ∅ ?_ ?_).trans ?_
    · intro s hs hne
      exfalso
      rw [Finset.mem_filter] at hs
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact absurd (hs.2.2 e he) (not_lt.2 (hall e))
    · intro h
      exfalso
      apply h
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · simp
      · simp
    · simp
  · rw [Set.indicator_apply, if_neg (show a ∉ {a | ∀ e, sdot e a ≤ y e} from hall)]
    push_neg at hall
    obtain ⟨es, -, hesmax⟩ := Finset.exists_max_image Finset.univ (fun e => sdot e a - y e)
      Finset.univ_nonempty
    obtain ⟨e1, he1⟩ := hall
    have hes : y es < sdot es a := by
      have h5 : sdot e1 a - y e1 ≤ sdot es a - y es := hesmax e1 (Finset.mem_univ _)
      linarith
    have key := sum_chains_eq_zero SLe sLe_refl sLe_trans (fun e => y e < sdot e a) es hes
      (fun e => sMeet e es) (fun e => sMeet_le_left e es) (fun e => sMeet_le_right e es)
      (fun x e h h' => le_sMeet x e es h h')
      (fun e he => by
        have hPos := hy'.2 e es
        have hdot := sdot_meet_join e es a
        have hjoin : sdot (sJoin e es) a - y (sJoin e es) ≤ sdot es a - y es :=
          hesmax (sJoin e es) (Finset.mem_univ _)
        show y (sMeet e es) < sdot (sMeet e es) a
        have he' : y e < sdot e a := he
        linarith)
    convert key

end Signs

end GlobalTheory.CompanionTheory.ChainInd

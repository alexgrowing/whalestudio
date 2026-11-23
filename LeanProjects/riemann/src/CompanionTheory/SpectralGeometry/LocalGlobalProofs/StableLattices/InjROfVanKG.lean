import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FilterAll
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KoszulDifferentialAnticommutator
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.WtProj

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhInjR

open CompanionTheory.D.LK CompanionTheory.D.LK.Car CompanionTheory.RgExh.U
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit)
open PI.UpqRep (rhoC)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem suppIn_sub {P : Pos n → Prop} {x y : Cn n V} (hx : SuppIn P x) (hy : SuppIn P y) : SuppIn P (x - y) := by
  intro A hA
  by_cases h : x A = 0
  · exact hy A fun h' => hA (by simp [h, h'])
  · exact hx A h

theorem suppIn_sum {ι : Type} {P : Pos n → Prop} (s : Finset ι) (f : ι → Cn n V) (h : ∀ b ∈ s, SuppIn P (f b)) :
    SuppIn P (∑ b ∈ s, f b) := by
  intro A hA
  rw [Finset.sum_apply] at hA
  obtain ⟨b, hb, h'⟩ := exists_ne_zero_of_sum_ne_zero hA
  exact h b hb A h'

theorem suppIn_bd {P : Pos n → Prop}
    (hP : ∀ i j k : Pos n, i.1.2 = j.1.1 → k.1.1 = i.1.1 → k.1.2 = j.1.2 → P i → P j → P k)
    (E : Fin n → Fin n → Module.End ℂ V) {x : Cn n V} (hx : SuppIn P x) : SuppIn P (bd (allT n) E x) := by
  intro A hA l hl
  rcases bd_ne _ E x A hA with ⟨i, -, h1⟩ | ⟨i, j, k, ht, h1⟩
  · exact hx _ (ann_ne h1).2 l (mem_insert_of_mem hl)
  · have h5 := (tri_ne h1).2.2.2
    by_cases hk : l = k
    · subst hk
      exact hP i j l ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2 (hx _ h5 i (mem_insert_self _ _))
        (hx _ h5 j (mem_insert_of_mem (mem_insert_self _ _)))
    · exact hx _ h5 l (mem_insert_of_mem (mem_insert_of_mem (mem_erase.2 ⟨hk, hl⟩)))

theorem inR_closed {ε : Fin n → Bool} {lev : Fin n → ℕ} (hm : Monotone lev) (i j k : Pos n) (e1 : i.1.2 = j.1.1)
    (e2 : k.1.1 = i.1.1) (e3 : k.1.2 = j.1.2) (hi : inR ε lev i) (hj : inR ε lev j) : inR ε lev k := by
  have m1 : lev i.1.1 ≤ lev i.1.2 := hm i.2.le
  have m2 : lev j.1.1 ≤ lev j.1.2 := hm j.2.le
  have m3 : lev i.1.2 = lev j.1.1 := congrArg lev e1
  rcases hi with hi | hi
  · rcases hj with hj | hj
    · left
      show ε k.1.1 = ε k.1.2
      rw [e2, e3, hi, e1]
      exact hj
    · right
      show lev k.1.1 < lev k.1.2
      rw [e2, e3]
      omega
  · right
    show lev k.1.1 < lev k.1.2
    rw [e2, e3]
    rcases hj with hj | hj <;> omega

theorem injR_of_vanKG (hV : VanKG) : InjR := by
  intro n ε γ lev V _ _ E hG hgl hU hF hmin u y hu hsupp hy hb
  have hE : KRel ε E := fun a b c d _ _ => hgl a b c d
  have hA : KRel (allT n) E := fun a b c d _ _ => hgl a b c d
  set τ := xv ε γ with hτ
  have hc := differential_commutes_weight_operator n _ (allT n) V E (fun _ _ h => h) hA
  obtain ⟨-, -, -, s4⟩ := differential_bounded_support n ε V E
  have hcl := inR_closed (ε := ε) hG.2.1
  have main : ∀ N (y : Cn n V), (∀ A, y A ≠ 0 → A.card = (om ε).card + 1 ∧ pot (A.filter fun i => ¬cpt ε i) < N) →
      SuppIn (inR ε lev) y → Wt (allT n) E τ y → bd (allT n) E y = Pi.single (om ε) u → u = 0 := by
    intro N
    induction N with
    | zero =>
      intro y h _ _ hb
      obtain rfl : y = 0 := funext fun A => by by_contra h'; exact Nat.not_lt_zero _ (h A h').2
      simpa using (congrFun hb (om ε)).symm
    | succ N ih =>
      intro y h hys hw hb
      let r : Finset (Pos n) → Cn n V := fun B A => if (A.filter fun i => ¬cpt ε i) = B then y A else 0
      have hr : ∀ B, Sup ε B ((om ε).card + 1 - B.card) (r B) := fun B A hA => by
        obtain ⟨h1, h2⟩ : (A.filter fun i => ¬cpt ε i) = B ∧ y A ≠ 0 := by
          simp only [r] at hA
          split_ifs at hA with h1
          · exact ⟨h1, hA⟩
          · exact absurd rfl hA
        have := card_filter_add_card_filter_not (s := A) (cpt ε)
        have := (h A h2).1
        exact ⟨h1, by rw [← h1]; omega⟩
      have hsum : y = ∑ B, r B := funext fun A => by simp [r, Finset.sum_apply]
      have hrne : ∀ B A, r B A ≠ 0 → pot B < N + 1 ∧ B.Nonempty ∧ B.card ≤ (om ε).card + 1 := fun B A hA => by
        have h2 : y A ≠ 0 := fun h' => hA (by simp [r, h'])
        have h3 := (hr B A hA).1
        have h4 := h A h2
        refine ⟨h3 ▸ h4.2, nonempty_iff_ne_empty.2 fun hB => ?_, h4.1 ▸ h3 ▸ card_filter_le _ _⟩
        have : A ⊆ om ε := fun i hi => mem_filter.2 ⟨mem_univ _, by
          by_contra hc; exact notMem_empty i (hB ▸ h3 ▸ mem_filter.2 ⟨hi, hc⟩)⟩
        have := card_le_card this
        omega
      have hex : ∀ B, ∃ t : Cn n V, Wt (allT n) E τ t ∧ (pot B = N → bd ε E t = r B) ∧ (pot B ≠ N → t = 0) ∧
          (t = 0 ∨ (B.card ≤ (om ε).card + 1 ∧ Sup ε B ((om ε).card + 1 - B.card + 1) t)) ∧
          SuppIn (inR ε lev) t := by
        intro B
        by_cases h0 : pot B = N ∧ r B ≠ 0
        · obtain ⟨A₀, hA₀⟩ := Function.ne_iff.1 h0.2
          obtain ⟨-, hBn, hBc⟩ := hrne B A₀ hA₀
          have hBU : ∀ i ∈ B, inU lev i := fun i hi => by
            have h2 : y A₀ ≠ 0 := fun h' => hA₀ (by simp [r, h'])
            have h3 := (hr B A₀ hA₀).1
            rw [← h3] at hi
            obtain ⟨hi1, hi2⟩ := mem_filter.1 hi
            exact (hys A₀ h2 i hi1).resolve_left hi2
          obtain ⟨t, t1, t2, t3⟩ := hV n ε γ lev V E hG hE hU hF hmin B _ (r B) hBn hBU (hr B) (fun c => funext fun A => by
              have := congrFun (hw c) A
              simp only [Ft_apply, Pi.smul_apply, r] at this ⊢
              split_ifs
              · exact this
              · simp) (funext fun A => by
              by_contra hne
              have hAB := (sup_bd E (hr B) hne).1
              have e := congrFun hb A
              have hAo : A ≠ om ε := by
                rintro rfl
                obtain ⟨i, hi⟩ := hBn
                rw [← hAB] at hi
                exact (mem_filter.1 hi).2 (mem_filter.1 (mem_filter.1 hi).1).2
              rw [Pi.single_eq_of_ne hAo, hsum, map_sum, Finset.sum_apply, Finset.sum_eq_single B] at e
              · apply hne
                by_contra h'
                have := (s4 B _ _ (hr B) A (by rw [Pi.sub_apply, e, zero_sub]; exact neg_ne_zero.2 hne)).1
                rw [hAB] at this
                exact lt_irrefl _ this
              · intro B' _ hB'
                by_cases h1 : r B' = 0
                · simp [h1]
                obtain ⟨A₁, hA₁⟩ := Function.ne_iff.1 h1
                have h2 := (hrne B' A₁ hA₁).1
                have h3 : bd ε E (r B') A = 0 := by
                  by_contra h3; exact hB' ((sup_bd E (hr B') h3).1.symm.trans hAB)
                by_contra h4
                have := (s4 B' _ _ (hr B') A (by rw [Pi.sub_apply, h3, sub_zero]; exact h4)).1
                rw [hAB] at this
                omega
              · simp)
          refine ⟨t, t2, fun _ => t3, fun h => absurd h0.1 h, Or.inr ⟨hBc, t1⟩, fun A hA i hi => ?_⟩
          by_cases hci : cpt ε i
          · exact Or.inl hci
          · exact Or.inr (hBU i ((t1 A hA).1 ▸ mem_filter.2 ⟨hi, hci⟩))
        · refine ⟨0, fun c => by simp, fun h => ?_, fun _ => rfl, Or.inl rfl, fun A hA => absurd rfl hA⟩
          rw [map_zero]
          by_contra h'
          exact h0 ⟨h, Ne.symm h'⟩
      choose t t1 t2 t3 t4 t5 using hex
      refine ih (y - ∑ B, bd (allT n) E (t B)) (fun A hA => ?_)
        (suppIn_sub hys (suppIn_sum _ _ fun B _ => suppIn_bd hcl E (t5 B))) (fun c => ?_) ?_
      · have e : (y - ∑ B, bd (allT n) E (t B)) A =
            ∑ B, ((if pot B = N then 0 else r B A) - (bd (allT n) E (t B) - bd ε E (t B)) A) := by
          rw [Pi.sub_apply, congrFun hsum A, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun B _ => ?_
          split_ifs with h1
          · rw [Pi.sub_apply, t2 B h1]; abel
          · simp [t3 B h1]
        rw [e] at hA
        obtain ⟨B, -, hB⟩ := exists_ne_zero_of_sum_ne_zero hA
        by_cases h1 : pot B = N
        · rw [if_pos h1, zero_sub, neg_ne_zero] at hB
          rcases t4 B with h2 | h2
          · simp [h2] at hB
          · have := s4 B _ _ h2.2 A hB
            have := h2.1
            omega
        · rw [if_neg h1, t3 B h1] at hB
          have hB' : r B A ≠ 0 := by simpa using hB
          have h2 := (hrne B A hB').1
          have h3 := (hr B A hB').1
          exact ⟨(h A fun h' => hB' (by simp [r, h'])).1, by rw [h3]; omega⟩
      · rw [map_sub, map_sum, hw c, smul_sub, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [← Module.End.mul_apply, (hc c).eq, Module.End.mul_apply, t1 B c, map_smul]
      · rw [map_sub, map_sum, hb, Finset.sum_eq_zero, sub_zero]
        exact fun B _ => LinearMap.congr_fun (koszul_differential_sq_zero n _ V E hA) _
  obtain ⟨y', y1, y2, y3⟩ := GlobalTheory.CompanionTheory.LKWtProj.wtProj n (allT n) ε V E hE hU hF _ hc τ y (fun c => funext fun A => by
    rw [hb, Ft_apply, filter_all]
    by_cases e : A = om ε
    · subst e
      rw [Pi.smul_apply, Pi.single_eq_same, hu c, wt_om, ← add_smul, hτ]
      simp [xv]
    · simp [Pi.single_eq_of_ne e])
  refine main ((univ.sup fun A : Finset (Pos n) => pot A) + 1) y' (fun A hA => ⟨?_, ?_⟩)
    (fun A hA => hsupp A fun h => hA (y3 A h)) y1 (y2.trans hb)
  · have := (hy A fun h => hA (y3 A h)).2
    rwa [filter_all] at this
  · exact Nat.lt_succ_of_le (Finset.le_sup (f := fun A : Finset (Pos n) => pot A) (mem_univ _))

end GlobalTheory.CompanionTheory.RgExhInjR

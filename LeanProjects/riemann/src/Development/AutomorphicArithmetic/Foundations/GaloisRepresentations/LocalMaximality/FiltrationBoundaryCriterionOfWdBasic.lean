import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {σ E : Type} [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E]

private lemma wd_apply' (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]

private lemma wd_congr' (w : σ → Module.End ℂ E) (c c' : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, w i = 0 ∨ c (t.erase i) = c' (t.erase i)) : wd w c t = wd w c' t := by
  rw [wd_apply', wd_apply']
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases h i hi with h | h
  · simp [h]
  · rw [h]

private lemma card_erase_mem' {Q t : Finset σ} {i : σ} (hi : i ∈ t) (hQ : i ∈ Q) :
    (((t.erase i) ∩ Q).card : ℤ) = ((t ∩ Q).card : ℤ) - 1 := by
  have h1 : (t.erase i) ∩ Q = (t ∩ Q).erase i := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  have h2 : i ∈ t ∩ Q := Finset.mem_inter.2 ⟨hi, hQ⟩
  have h3 : 0 < (t ∩ Q).card := Finset.card_pos.2 ⟨i, h2⟩
  rw [h1, Finset.card_erase_of_mem h2]
  omega

private lemma card_erase_not' {Q t : Finset σ} {i : σ} (hQ : i ∉ Q) :
    (t.erase i) ∩ Q = t ∩ Q := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩
    exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨fun e => hQ (e ▸ h'), h⟩, h'⟩

private lemma levQ' (w : σ → Module.End ℂ E) (Q : Finset σ) {m m' : ℤ} (hm : m' = m + 1)
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m') (wd (wOn Q w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m') := ht
  have h0 : wd (wOn Q w) y t = wd (wOn Q w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · right
      refine hy _ ?_
      have h1 := card_erase_mem' hi hiQ
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      omega
    · left
      simp [wOn, hiQ]
  rw [h0, map_zero]
  rfl

private lemma levC' (w : σ → Module.End ℂ E) (Q : Finset σ) {m : ℤ}
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m) (wd (wOn Qᶜ w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m) := ht
  have h0 : wd (wOn Qᶜ w) y t = wd (wOn Qᶜ w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · left
      simp [wOn, hiQ]
    · right
      refine hy _ ?_
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      rw [card_erase_not' hiQ]
      exact ht'
  rw [h0, map_zero]
  rfl

private lemma wd_split' (hW : WdBasic) (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E)
    (Q : Finset σ) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = wd (wOn Q w) c t + wd (wOn Qᶜ w) c t := by
  have h := (hW σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w)
  have h2 : wOn Q w + wOn Qᶜ w = w := by
    funext i
    by_cases hi : i ∈ Q <;> simp [wOn, hi]
  rw [h2] at h
  rw [h]
  rfl

private lemma sub_cocycle' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    (hcx : (acx A w).IsCx) {n : ℤ} {c y : Finset σ → E} (hc : c ∈ (acx A w).Z n)
    (hy : y ∈ (acx A w).C (n - 1)) : c - wd w y ∈ (acx A w).Z n := by
  obtain ⟨h1, h2⟩ := hcx _ y hy
  rw [sub_add_cancel] at h1
  obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hc1 h1, ?_⟩
  have h3 : wd w c = 0 := hc2
  have h4 : wd w (wd w y) = 0 := h2
  show wd w (c - wd w y) = 0
  rw [map_sub, h3, h4, sub_zero]

private lemma of_sub' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E} {n : ℤ}
    {c y : Finset σ → E} (hy : y ∈ (acx A w).C (n - 1)) (h : c - wd w y ∈ (acx A w).B n) :
    c ∈ (acx A w).B n := by
  have h2 : wd w y ∈ (acx A w).B n := Submodule.mem_map_of_mem hy
  simpa using add_mem h h2

private lemma low' (hW : WdBasic) {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {Q : Finset σ} {d : ℤ} (hok : WOk A w) (hq : QEx A w Q d) :
    ∀ k : ℕ, k ≤ d.toNat → ∀ (n : ℤ) (c : Finset σ → E), c ∈ (acx A w).Z n →
      Lev Q (· ≤ (k : ℤ) - 1) c → c ∈ (acx A w).B n := by
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  intro k
  induction k with
  | zero =>
    intro _ n c hc hl
    have h0 : c = 0 := by
      funext s
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((0 : ℕ) : ℤ) - 1)
      omega
    rw [h0]
    exact zero_mem _
  | succ k ih =>
    intro hk n c hc hl
    have hkd : (k : ℤ) < d := by omega
    have hl' : ∀ s, (k : ℤ) < ((s ∩ Q).card : ℤ) → c s = 0 := by
      intro s hs
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - 1)
      push_cast
      omega
    obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
    have hc3 : wd w c = 0 := hc2
    let cm : Finset σ → E := fun s => if ((s ∩ Q).card : ℤ) = k then c s else 0
    have hcm : cm ∈ (acx A w).C n := by
      refine Submodule.mem_pi.2 fun s hs => ?_
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · have : cm s = c s := if_pos h
        rw [this]
        exact Submodule.mem_pi.1 hc1 s hs
      · have : cm s = 0 := if_neg h
        rw [this]
        exact zero_mem _
    have hcl : Lev Q (· = (k : ℤ)) cm := fun s hs => if_neg hs
    have hkill : wd (wOn Q w) cm = 0 := by
      funext t
      by_cases ht : ((t ∩ Q).card : ℤ) = k + 1
      · have e1 : wd (wOn Q w) cm t = wd (wOn Q w) c t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · right
            have h1 := card_erase_mem' hi hiQ
            exact if_pos (by omega)
          · left
            simp [wOn, hiQ]
        have e2 : wd (wOn Qᶜ w) c t = wd (wOn Qᶜ w) 0 t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · left
            simp [wOn, hiQ]
          · right
            refine hl' _ ?_
            rw [card_erase_not' hiQ]
            omega
        have e3 := wd_split' hW A w Q c t
        rw [hc3, e2, map_zero] at e3
        rw [e1]
        simpa using e3.symm
      · exact levQ' w Q rfl hcl t ht
    obtain ⟨y, hy, hyl, hyd⟩ := hq n k hkd cm hcm hcl hkill
    refine of_sub' hy (ih (by omega) n _ (sub_cocycle' hcx hc hy) ?_)
    intro s hs
    have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (k : ℤ) - 1) := hs
    have e1 := wd_split' hW A w Q y s
    have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
      show ¬ (((s ∩ Q).card : ℤ) = (k : ℤ) - 1)
      omega)
    have e3 : wd (wOn Q w) y s = cm s := congrFun hyd s
    have e4 : cm s = c s := by
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · exact if_pos h
      · have : cm s = 0 := if_neg h
        rw [this, hl' s (by omega)]
    show c s - wd w y s = 0
    rw [e1, e2, e3, e4, add_zero, sub_self]

end

theorem UpperTheory.Gal.productCup_of_system.filtrationBoundaryCriterion_of_wdBasic :
    WdBasic → FiltrationBoundaryCriterion := by
  intro hW σ E _ _ _ _ A w Q d n hok hq c hc hl hy0
  obtain ⟨y, hy, hyl, hyd⟩ := hy0
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  have hl' : ∀ s, d < ((s ∩ Q).card : ℤ) → c s = 0 := by
    intro s hs
    refine hl s ?_
    show ¬ (((s ∩ Q).card : ℤ) ≤ d)
    omega
  refine of_sub' hy (low' hW hok hq d.toNat le_rfl n _ (sub_cocycle' hcx hc hy) ?_)
  intro s hs
  have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (d.toNat : ℤ) - 1) := hs
  have hge : d ≤ ((s ∩ Q).card : ℤ) := by omega
  have e1 := wd_split' hW A w Q y s
  have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
    show ¬ (((s ∩ Q).card : ℤ) = d - 1)
    omega)
  show c s - wd w y s = 0
  rw [e1, e2, add_zero]
  by_cases h : ((s ∩ Q).card : ℤ) = d
  · rw [hyd s h, sub_self]
  · have e3 : wd (wOn Q w) y s = 0 := levQ' w Q (by ring) hyl s h
    rw [e3, hl' s (by omega), sub_self]

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChoiceOfTopsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParameterInequalitiesGoodStatement

open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain

namespace GlobalTheory.TopsChoice

open Formalism.FrobeniusOrbits Finset

lemma bern_eq_prod {α : Type} [Fintype α] [DecidableEq α] (δ : ℝ) (T : Finset α) :
    bern δ T = (∏ _a ∈ T, δ) * ∏ _a ∈ univ \ T, (1 - δ) := by
  simp [bern, Finset.card_univ_diff]

lemma fibre_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (δ : ℝ)
    (f : β → α) (hf : Function.Injective f) (S : Finset β) :
    ∑ T : Finset α, (if univ.filter (fun i => f i ∈ T) = S then bern δ T else 0) = bern δ S := by
  classical
  set g : α → ℝ := fun a => if a ∈ (univ \ S).image f then 0 else δ with hg
  set h : α → ℝ := fun a => if a ∈ S.image f then 0 else 1 - δ with hh
  have h1 := Finset.prod_add g h (univ : Finset α)
  rw [powerset_univ] at h1
  have h2 : ∏ a, (g a + h a) = bern δ S := by
    rw [← Finset.prod_subset (subset_univ ((univ : Finset β).image f)), prod_image hf.injOn]
    · rw [bern_eq_prod, ← prod_sdiff (subset_univ S), mul_comm]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        simp [hg, hh, hf.eq_iff, hi]
      · refine prod_congr rfl fun i hi => ?_
        have hi' : i ∉ S := (mem_sdiff.mp hi).2
        simp [hg, hh, hf.eq_iff, hi']
    · intro a _ ha
      have ha1 : a ∉ (univ \ S).image f := fun h' => ha (image_subset_image (subset_univ _) h')
      have ha2 : a ∉ S.image f := fun h' => ha (image_subset_image (subset_univ _) h')
      simp only [hg, hh, if_neg ha1, if_neg ha2]
      ring
  rw [← h2, h1]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hT
  · rw [bern_eq_prod]
    congr 1
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ (univ \ S).image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        exact (mem_sdiff.mp hi).2 (hT ▸ mem_filter.mpr ⟨mem_univ _, ha⟩)
      simp only [hg, if_neg this]
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ S.image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        rw [← hT] at hi
        exact (mem_sdiff.mp ha).2 (mem_filter.mp hi).2
      simp only [hh, if_neg this]
  · have : ∃ i, ¬ (f i ∈ T ↔ i ∈ S) := by
      by_contra hc
      push Not at hc
      exact hT (by ext i; simp [hc i])
    obtain ⟨i, hi⟩ := this
    by_cases hiS : i ∈ S
    · have hT' : f i ∉ T := fun h' => hi ⟨fun _ => hiS, fun _ => h'⟩
      rw [prod_eq_zero (s := univ \ T) (i := f i) (by simp [hT']), mul_zero]
      simp only [hh, if_pos (mem_image_of_mem f hiS)]
    · have hT' : f i ∈ T := by
        by_contra h'
        exact hi ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hiS⟩
      rw [prod_eq_zero (s := T) (i := f i) hT', zero_mul]
      simp only [hg, if_pos (mem_image_of_mem f (mem_sdiff.mpr ⟨mem_univ i, hiS⟩))]

lemma marginal {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (δ : ℝ)
    (f : β → α) (hf : Function.Injective f) (A : Finset β → Prop) [DecidablePred A] :
    ∑ T : Finset α, (if A (univ.filter (fun i => f i ∈ T)) then bern δ T else 0) =
      ∑ S : Finset β, if A S then bern δ S else 0 := by
  calc ∑ T : Finset α, (if A (univ.filter (fun i => f i ∈ T)) then bern δ T else 0)
      = ∑ T : Finset α, ∑ S : Finset β,
          (if univ.filter (fun i => f i ∈ T) = S then (if A S then bern δ T else 0) else 0) := by
        refine sum_congr rfl fun T _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ S : Finset β, if A S then bern δ S else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        by_cases hA : A S
        · simp only [if_pos hA]
          exact fibre_sum δ f hf S
        · simp [hA]

open Classical in
lemma fin_sum_eq (n : ℕ) (δ : ℝ) (i₀ : Fin n) (A : Finset ℕ → Prop) :
    (∑ S : Finset (Fin n), if i₀ ∈ S ∧ A (S.map Fin.valEmbedding) then bern δ S else 0) =
      Formalism.G0.condProbAt n δ i₀ A * δ := by
  unfold Formalism.G0.condProbAt
  rw [sum_mul]
  refine Finset.sum_bij (fun S _ => S.map Fin.valEmbedding) ?_ ?_ ?_ ?_
  · intro S _
    rw [mem_powerset]
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    simp
  · intro S _ S' _ h
    exact Finset.map_injective _ h
  · intro T hT
    refine ⟨univ.filter (fun i : Fin n => (i : ℕ) ∈ T), mem_univ _, ?_⟩
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      exact ⟨⟨x, mem_range.mp (mem_powerset.mp hT hx)⟩, hx, rfl⟩
  · intro S _
    have hm : (i₀ : ℕ) ∈ S.map Fin.valEmbedding ↔ i₀ ∈ S :=
      Finset.mem_map' Fin.valEmbedding
    simp only [hm]
    split_ifs with h
    · have hc : 1 ≤ S.card := card_pos.mpr ⟨i₀, h.1⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc
      simp only [bern, card_map, Fintype.card_fin, hk, Nat.add_sub_cancel]
      ring
    · simp

open Classical in

lemma orbit_sum {α : Type} [Fintype α] [DecidableEq α] [AddCommGroup α] (δ : ℝ) (b h t : α)
    (ht : ∃ i : ℕ, b + i • h = t) (A : Finset ℕ → Prop) :
    ∃ i₀ < addOrderOf h,
      (∑ T : Finset α, if t ∈ T ∧ A ((univ.filter
          (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding)
        then bern δ T else 0) = Formalism.G0.condProbAt (addOrderOf h) δ i₀ A * δ := by
  obtain ⟨i, hi⟩ := ht
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have hlt : i % addOrderOf h < addOrderOf h := Nat.mod_lt _ hpos
  refine ⟨i % addOrderOf h, hlt, ?_⟩
  have hinj : Function.Injective (fun j : Fin (addOrderOf h) => b + (j : ℕ) • h) := by
    intro j k hjk
    have := add_left_cancel hjk
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf j.2 k.2 this)
  rw [← fin_sum_eq (addOrderOf h) δ ⟨_, hlt⟩ A, ← marginal δ _ hinj
    (fun S => (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ S ∧ A (S.map Fin.valEmbedding))]
  refine sum_congr rfl fun T _ => ?_
  have : t ∈ T ↔ (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ univ.filter
      (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T) := by
    simp [mod_addOrderOf_nsmul, hi]
  simp only [this]

end GlobalTheory.TopsChoice

namespace GlobalTheory

open GlobalTheory.TopsChoice

theorem topsChoice : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ e L₂ : ℕ, s.x ^ Formalism.MainNotions.G.hG s / 2 ≤ ((2 ^ e : ℕ) : ℝ) → ((2 ^ e : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → ∀ bs : ZMod (2 ^ e) → ZMod (2 ^ e) → ZMod (2 ^ e), (∀ h t, ∃ i : ℕ, bs h t + i • h = t) → (∀ h t, bs h (t + h) = bs h t) → ∀ (PP : Finset ℕ) (hp : ℕ → ZMod (2 ^ e)) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, s.x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) → ∃ TT : Finset (ZMod (2 ^ e)), s.delta1 * ((2 ^ e : ℕ) : ℝ) / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * ((2 ^ e : ℕ) : ℝ) ∧ ∑ p ∈ PP, ω p * (({t : ZMod (2 ^ e) | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * ((2 ^ e : ℕ) : ℝ) * ∑ p ∈ PP, ω p := by
  classical
  intro eps he he'
  obtain ⟨Cb, x₀, hCb, hnum⟩ := GlobalTheory.T.parameter_inequalities_good eps he he'
  refine ⟨Cb, max x₀ 32, hCb, ?_⟩
  intro s hs hx e L₂ hlo hhi hL bs hbs _ PP hp ω hω hPP
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hx32 : 32 ≤ s.x := le_trans (le_max_right _ _) hx
  have hδ : 0 < s.delta1 := Real.rpow_pos_of_pos hx0 _
  have hδ1 : s.delta1 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by have := s.eps_pos; linarith)
  haveI : NeZero (2 ^ e) := ⟨by positivity⟩
  have hcard : Fintype.card (ZMod (2 ^ e)) = 2 ^ e := ZMod.card _
  have h16 : 16 ≤ s.delta1 * (Fintype.card (ZMod (2 ^ e)) : ℝ) := by
    rw [hcard]
    have h1 : s.x ≤ s.delta1 * s.x ^ Formalism.MainNotions.G.hG s := by
      unfold Scale.delta1 Formalism.MainNotions.G.hG
      rw [← Real.rpow_add hx0]
      calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1.le (by have := s.eps_pos; linarith)
    have := mul_le_mul_of_nonneg_left hlo hδ.le
    linarith
  have hβ : 0 ≤ Cb * s.x ^ (-2 : ℝ) := by positivity
  obtain ⟨T, hT1, hT2, hT3⟩ := Formalism.FrobeniusOrbits.hostTops (ZMod (2 ^ e)) PP s.delta1 (Cb * s.x ^ (-2 : ℝ))
    (fun p => ω p)
    (fun p t T => ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter
      (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (Formalism.MainNotions.G.KG s)
      (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
    hδ hδ1 hβ (fun p => hω p) h16 (by
      intro p t
      have hn : ((addOrderOf (hp p) : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s := by
        refine le_trans ?_ hhi
        exact Nat.cast_le.mpr (addOrderOf_le_card_univ.trans hcard.le)
      obtain ⟨h1, h2⟩ := hnum s hs (le_trans (le_max_left _ _) hx) (addOrderOf (hp p)) L₂
        (hPP p p.2) hn hL
      obtain ⟨i₀, hi₀, hsum⟩ := orbit_sum s.delta1 (bs (hp p) t) (hp p) t (hbs _ _)
        (fun T => ¬ Formalism.G0.GoodOrbitIntervalTileCondition (addOrderOf (hp p)) T L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s)
          (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x)
          (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
          (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x))
      have hu : 1 ≤ Formalism.MainNotions.G.goodU s.delta1 := Nat.ceil_pos.mpr (by positivity)
      have h3 := GlobalTheory.T.choice_of_tops (addOrderOf (hp p)) s.delta1 L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s)
        (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x)
        (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
        (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x) i₀ hδ.le hδ1
        (Nat.le_add_left 1 _) hu h1 hi₀
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (h3.trans h2) hδ.le)
      rw [← hsum]
      unfold Formalism.MainNotions.G.IsGoodOrbit
      convert rfl)
  rw [hcard] at hT1 hT2 hT3
  refine ⟨T, hT1, hT2, ?_⟩
  rw [← Finset.sum_coe_sort PP, ← Finset.sum_coe_sort PP ω]
  refine le_trans (le_of_eq ?_) hT3
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  rw [← Set.ncard_coe_finset, Finset.coe_filter]

end GlobalTheory

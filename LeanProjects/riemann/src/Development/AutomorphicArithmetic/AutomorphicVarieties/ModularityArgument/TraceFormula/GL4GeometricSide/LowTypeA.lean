import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Finset PositivityTheory.RgBcC.RealD PositivityTheory.Rg.Cz

namespace UpperTheory.V.Z.GSp4Splitting.Low

variable {n : ℕ}

def ev (a : Fin n) : Fin n → ℝ := fun x => if x = a then 1 else 0

abbrev Cone (Q : Fin n → ℝ) : Prop := inCone (fun a : Fin n => (a : ℕ)) Q

theorem cone_zero : Cone (0 : Fin n → ℝ) := ⟨fun _ _ => 0, fun _ _ h => absurd rfl h, fun x => by simp⟩

theorem Cone.add {Q R : Fin n → ℝ} (hQ : Cone Q) (hR : Cone R) : Cone (Q + R) := by
  obtain ⟨c, hc, eQ⟩ := hQ
  obtain ⟨d, hd, eR⟩ := hR
  refine ⟨fun a b => c a b + d a b, fun a b h => ?_, fun x => ?_⟩
  · by_cases h1 : c a b = 0
    · exact hd a b (by simpa [h1] using h)
    · exact hc a b h1
  · rw [Pi.add_apply, eQ, eR, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    push_cast
    ring

theorem cone_root {a b : Fin n} (h : a < b) : Cone (ev a - ev b) := by
  refine ⟨fun c d => if c = a ∧ d = b then 1 else 0, fun c d hcd => ?_, fun x => ?_⟩
  · by_cases h1 : c = a ∧ d = b
    · rw [h1.1, h1.2]; exact h
    · exact absurd (if_neg h1) hcd
  · rw [sum_eq_single a, sum_eq_single b]
    · simp [ev]
    · intro d _ hd; simp [hd]
    · simp
    · intro c _ hc; simp [hc]
    · simp

theorem cone_sum {α : Type} (T : Finset α) (f : α → Fin n → ℝ) (h : ∀ p ∈ T, Cone (f p)) : Cone (∑ p ∈ T, f p) :=
  Finset.sum_induction f Cone (fun _ _ => Cone.add) cone_zero h

theorem cone_sets (A B : Finset (Fin n)) (hc : A.card = B.card) (h : ∀ x ∈ A, x ∉ B → ∀ y ∈ B, y ∉ A → x < y) :
    Cone (∑ x ∈ A, ev x - ∑ y ∈ B, ev y) := by
  rw [← sum_sdiff_sub_sum_sdiff]
  have hd : (A \ B).card = (B \ A).card := card_sdiff_comm hc
  let φ := Finset.equivOfCardEq hd
  rw [← sum_coe_sort (A \ B), ← sum_coe_sort (B \ A), ← Equiv.sum_comp φ, ← sum_sub_distrib]
  refine cone_sum _ _ fun x _ => cone_root ?_
  have h1 := mem_sdiff.1 x.2
  have h2 := mem_sdiff.1 (φ x).2
  exact h _ h1.1 h1.2 _ h2.1 h2.2

theorem cone_maps {α : Type} (T : Finset α) (f g : α → Fin n) (hf : Set.InjOn f T) (hg : Set.InjOn g T)
    (h : ∀ p ∈ T, (∀ q ∈ T, g q ≠ f p) → ∀ q ∈ T, (∀ p ∈ T, f p ≠ g q) → f p < g q) :
    Cone (∑ p ∈ T, (ev (f p) - ev (g p))) := by
  rw [sum_sub_distrib, ← sum_image (f := ev) hf, ← sum_image (f := ev) hg]
  refine cone_sets _ _ (by rw [card_image_of_injOn hf, card_image_of_injOn hg]) ?_
  intro x hx hx' y hy hy'
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
  obtain ⟨q, hq, rfl⟩ := mem_image.1 hy
  exact h p hp (fun q hq e => hx' (mem_image.2 ⟨q, hq, e⟩)) q hq fun p hp e => hy' (mem_image.2 ⟨p, hp, e⟩)

theorem cone_cols {P C : Type} [DecidableEq C] (col : P → C) (b I : P → Fin n) (S : Finset P)
    (hS : ∀ p q, col p = col q → p ∈ S → q ∈ S) (hb : IsTab col b) (hI : ∀ p q, col p = col q → I p = I q → p = q) :
    Cone (∑ p ∈ S, (ev (I p) - ev (b p))) ∧ Cone (∑ p ∈ S, (ev (b p).rev - ev (I p))) := by
  have inj : ∀ (f : P → Fin n), (∀ p q, col p = col q → f p = f q → p = q) → ∀ c,
      Set.InjOn f (S.filter fun p => col p = c) := fun f hf c p hp q hq e =>
    hf p q ((mem_filter.1 hp).2.trans (mem_filter.1 hq).2.symm) e
  have up : ∀ c, ∀ q ∈ S.filter (fun p => col p = c), ∀ i, b q < i → ∃ r ∈ S.filter (fun p => col p = c), b r = i := by
    intro c q hq i hi
    obtain ⟨r, hr, e⟩ := hb.2 q i hi
    exact ⟨r, mem_filter.2 ⟨hS q r hr.symm (mem_filter.1 hq).1, hr.trans (mem_filter.1 hq).2⟩, e⟩
  constructor
  · rw [← sum_fiberwise_of_maps_to (g := col) (t := S.image col) fun p hp => mem_image_of_mem _ hp]
    refine cone_sum _ _ fun c _ => cone_maps _ _ _ (inj I hI c) (inj b hb.1 c) fun p _ h1 q hq _ => ?_
    rcases lt_trichotomy (I p) (b q) with h | h | h
    · exact h
    · exact absurd h.symm (h1 q hq)
    · obtain ⟨r, hr, e⟩ := up c q hq _ h
      exact absurd e (h1 r hr)
  · rw [← sum_fiberwise_of_maps_to (g := col) (t := S.image col) fun p hp => mem_image_of_mem _ hp]
    refine cone_sum _ _ fun c _ => cone_maps _ (fun p => (b p).rev) _
      (inj _ (fun p q h e => hb.1 p q h (Fin.rev_injective e)) c) (inj I hI c) fun p hp _ q _ h2 => ?_
    rcases lt_trichotomy (b p).rev (I q) with h | h | h
    · exact h
    · exact absurd h (h2 p hp)
    · obtain ⟨r, hr, e⟩ := up c p hp (I q).rev (Fin.lt_rev_iff.1 h)
      exact absurd (by rw [e, Fin.rev_rev]) (h2 r hr)

theorem two_rho : (fun a : Fin n => ((n : ℝ) - 1) - 2 * (a : ℕ)) =
    ∑ x : Fin n × Fin n, if x.1 < x.2 then ev x.1 - ev x.2 else 0 := by
  funext a
  have h1 : ∑ c : Fin n, ∑ d : Fin n, (if c < d then ev c a else 0) = ((Ioi a).card : ℝ) := by
    rw [sum_eq_single a]
    · simp [ev, filter_lt_eq_Ioi]
    · intro c _ hc; simp [ev, Ne.symm hc]
    · simp
  have h2 : ∑ c : Fin n, ∑ d : Fin n, (if c < d then ev d a else 0) = ((Iio a).card : ℝ) := by
    rw [sum_comm, sum_eq_single a]
    · simp [ev, filter_gt_eq_Iio]
    · intro c _ hc; simp [ev, Ne.symm hc]
    · simp
  have h3 : ∀ c d : Fin n, (if c < d then ev c - ev d else 0) a =
      (if c < d then ev c a else 0) - (if c < d then ev d a else 0) := fun c d => by split_ifs <;> simp
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [h3, sum_sub_distrib, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  have := a.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

theorem cone_pairs {α : Type} (T : Finset α) (r : α → Fin n × Fin n) (hr : Set.InjOn r T) :
    Cone ((fun a : Fin n => ((n : ℝ) - 1) - 2 * (a : ℕ)) - ∑ k ∈ T, (ev (r k).1 - ev (r k).2)) := by
  rw [← sum_image (f := fun x : Fin n × Fin n => ev x.1 - ev x.2) hr, two_rho, ← univ_inter (T.image r),
    ← sum_ite_mem, ← sum_sub_distrib]
  refine cone_sum _ _ fun x _ => ?_
  split_ifs with h1 h2 h2
  · rw [sub_self]; exact cone_zero
  · rw [sub_zero]; exact cone_root h1
  · rw [zero_sub, neg_sub]
    rcases (not_lt.1 h1).lt_or_eq with h | h
    · exact cone_root h
    · rw [h, sub_self]; exact cone_zero
  · rw [sub_self]; exact cone_zero

end UpperTheory.V.Z.GSp4Splitting.Low

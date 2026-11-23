import Mathlib
import GroundTheory.AutomorphicForms.SatakeTriangular

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open Finset

variable {n : ℕ}

theorem antitone_of_forall_succ_le {f : Fin n → ℤ}
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j ≤ f i) : Antitone f := by
  have key : ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d → f b ≤ f a := by
    intro d
    induction d with
    | zero =>
      intro a b hab
      rw [show b = a from Fin.ext (by omega)]
    | succ d ih =>
      intro a b hab
      have hc : (a : ℕ) + d < n := by omega
      exact (h ⟨a + d, hc⟩ b (by simp only; omega)).trans (ih a ⟨a + d, hc⟩ rfl)
  intro a b hab
  exact key (b - a) a b (by have := Fin.le_def.1 hab; omega)

theorem lamS_apply (S : Finset (Fin n)) (i : Fin n) : lamS S i = if i ∈ S then 1 else 0 := rfl

theorem exists_ascent {l : Fin n → ℤ} (hl : Antitone l) {S : Finset (Fin n)}
    (h : ¬ Antitone (l + lamS S)) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i = l j ∧ i ∉ S ∧ j ∈ S := by
  by_contra hne
  push Not at hne
  apply h
  refine antitone_of_forall_succ_le fun i j hij => ?_
  have hle : l j ≤ l i := hl (Fin.le_def.2 (by omega))
  simp only [Pi.add_apply, lamS_apply]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp only [hi, hj, if_true, if_false]
  · omega
  · omega
  · rcases lt_or_eq_of_le hle with hlt | heq
    · omega
    · exact absurd hj (hne i j hij heq.symm hi)
  · omega

theorem add_lamS_comp_swap {l : Fin n → ℤ} {i j : Fin n} (hlij : l i = l j) (S : Finset (Fin n)) :
    (l + lamS S) ∘ Equiv.swap i j = l + lamS (S.map (Equiv.swap i j).toEmbedding) := by
  funext x
  simp only [Function.comp_apply, Pi.add_apply, lamS_apply, Finset.mem_map_equiv,
    Equiv.symm_swap]
  congr 1
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, hlij]
  · rw [h2, hlij]
  · rfl

theorem sum_val_map_swap {S : Finset (Fin n)} {i j : Fin n} (hij : (j : ℕ) = i + 1) (hi : i ∉ S)
    (hj : j ∈ S) :
    ∑ x ∈ S.map (Equiv.swap i j).toEmbedding, (x : ℕ) + 1 = ∑ x ∈ S, (x : ℕ) := by
  rw [Finset.sum_map]
  rw [← Finset.insert_erase hj, Finset.sum_insert (Finset.notMem_erase j S),
    Finset.sum_insert (Finset.notMem_erase j S)]
  have hrest : ∑ x ∈ S.erase j, ((Equiv.swap i j).toEmbedding x : ℕ) = ∑ x ∈ S.erase j, (x : ℕ) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxj : x ≠ j := Finset.ne_of_mem_erase hx
    have hxi : x ≠ i := fun h => hi (h ▸ Finset.mem_of_mem_erase hx)
    simp [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  rw [hrest]
  simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_right]
  omega

theorem exists_perm_antitone {V : Type*} (H : (Fin n → ℤ) → V)
    (hH : ∀ (μ : Fin n → ℤ) (i j : Fin n), (j : ℕ) = i + 1 → μ j = μ i + 1 →
      H (μ ∘ Equiv.swap i j) = H μ)
    {l : Fin n → ℤ} (hl : Antitone l) (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), Antitone ((l + lamS S) ∘ σ) ∧
      H ((l + lamS S) ∘ σ) = H (l + lamS S) := by
  suffices key : ∀ k, ∀ S : Finset (Fin n), ∑ x ∈ S, (x : ℕ) = k →
      ∃ σ : Equiv.Perm (Fin n), Antitone ((l + lamS S) ∘ σ) ∧
        H ((l + lamS S) ∘ σ) = H (l + lamS S) from key _ S rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S hk
    by_cases ha : Antitone (l + lamS S)
    · exact ⟨1, by simpa using ha, by simp⟩
    obtain ⟨i, j, hij, hlij, hiS, hjS⟩ := exists_ascent hl ha
    have hcomp := add_lamS_comp_swap hlij S
    have hsum := sum_val_map_swap hij hiS hjS
    obtain ⟨σ, hσ, hHσ⟩ := ih _ (by omega) (S.map (Equiv.swap i j).toEmbedding) rfl
    refine ⟨Equiv.swap i j * σ, ?_, ?_⟩
    · rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hcomp]
      exact hσ
    · rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hcomp, hHσ, ← hcomp]
      refine hH _ i j hij ?_
      simp only [Pi.add_apply, lamS_apply, hiS, hjS, if_true, if_false, hlij]
      ring

def initSeg {r : ℕ} (hr : r ≤ n) : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hr)

theorem mem_initSeg {r : ℕ} (hr : r ≤ n) {i : Fin n} : i ∈ initSeg hr ↔ (i : ℕ) < r := by
  simp only [initSeg, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    simp
  · intro h
    exact ⟨⟨i, h⟩, Fin.ext (by simp)⟩

theorem card_initSeg {r : ℕ} (hr : r ≤ n) : (initSeg hr).card = r := by
  simp [initSeg]

def tailSet {m : ℕ} (hm : m ≤ n) : Finset (Fin n) :=
  Finset.univ.map ⟨tailEmb hm, tailEmb_injective hm⟩

theorem card_tailSet {m : ℕ} (hm : m ≤ n) : (tailSet hm).card = m := by
  simp [tailSet]

theorem mem_tailSet {m : ℕ} (hm : m ≤ n) {i : Fin n} : i ∈ tailSet hm ↔ n - m ≤ (i : ℕ) := by
  simp only [tailSet, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, rfl⟩
    simp [tailEmb]
  · intro h
    exact ⟨⟨i - (n - m), by omega⟩, Fin.ext (by simp [tailEmb]; omega)⟩

theorem tailSum_eq_sum_tailSet (f : Fin n → ℤ) {m : ℕ} (hm : m ≤ n) :
    tailSum f hm = ∑ i ∈ tailSet hm, f i := by
  rw [tailSet, Finset.sum_map]
  rfl

theorem tailSum_add (f g : Fin n → ℤ) {m : ℕ} (hm : m ≤ n) :
    tailSum (f + g) hm = tailSum f hm + tailSum g hm := by
  simp only [tailSum, Pi.add_apply, Finset.sum_add_distrib]

theorem sum_lamS_eq_card (S A : Finset (Fin n)) :
    ∑ i ∈ A, lamS S i = ((A.filter (· ∈ S)).card : ℤ) := by
  simp only [lamS_apply]
  rw [Finset.sum_boole]

theorem card_tailSet_inter_initSeg_le {m r : ℕ} (hm : m ≤ n) (hr : r ≤ n) {A S : Finset (Fin n)}
    (hA : A.card = m) (hS : S.card = r) :
    ((tailSet hm).filter (· ∈ initSeg hr)).card ≤ (A.filter (· ∈ S)).card := by
  have hAS : A.filter (· ∈ S) = A ∩ S := Finset.filter_mem_eq_inter
  have hBT : (tailSet hm).filter (· ∈ initSeg hr) = tailSet hm ∩ initSeg hr :=
    Finset.filter_mem_eq_inter
  rw [hAS, hBT]
  have h1 := Finset.card_union_add_card_inter A S
  have h2 : (A ∪ S).card ≤ n := by
    simpa using Finset.card_le_univ (A ∪ S)
  by_cases hmr : r + m ≤ n
  · have : tailSet hm ∩ initSeg hr = ∅ := by
      ext i
      simp only [Finset.mem_inter, mem_tailSet, mem_initSeg, Finset.notMem_empty, iff_false,
        not_and]
      omega
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  · have h3 := Finset.card_union_add_card_inter (tailSet hm) (initSeg hr)
    have h4 : tailSet hm ∪ initSeg hr = Finset.univ := by
      ext i
      simp only [Finset.mem_union, mem_tailSet, mem_initSeg, Finset.mem_univ, iff_true]
      omega
    rw [h4, Finset.card_univ, Fintype.card_fin, card_tailSet, card_initSeg] at h3
    omega

theorem domLE_rearrangement {l : Fin n → ℤ} (hl : Antitone l) {r : ℕ} (hr : r ≤ n)
    {S : Finset (Fin n)} (hS : S.card = r) (σ : Equiv.Perm (Fin n)) :
    DomLE ((l + lamS S) ∘ σ) (l + lamS (initSeg hr)) := by
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [tailSum_add, tailSum_eq_sum_tailSet (lamS _), sum_lamS_eq_card,
      tailSum_eq_sum_tailSet ((l + lamS S) ∘ σ)]
    have hA : ((tailSet hm).map σ.toEmbedding).card = m := by
      rw [Finset.card_map, card_tailSet]
    have hsum : ∑ i ∈ tailSet hm, ((l + lamS S) ∘ σ) i =
        ∑ i ∈ (tailSet hm).map σ.toEmbedding, (l + lamS S) i := by
      rw [Finset.sum_map]
      rfl
    rw [hsum]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, sum_lamS_eq_card]
    have h1 := tailSum_le_sum hl hm _ hA
    have h2 := card_tailSet_inter_initSeg_le hm hr hA hS
    have h2' : (((tailSet hm).filter (· ∈ initSeg hr)).card : ℤ) ≤
        ((((tailSet hm).map σ.toEmbedding).filter (· ∈ S)).card : ℤ) := by exact_mod_cast h2
    linarith
  · show ∑ i, (l + lamS S) (σ i) = _
    rw [Equiv.sum_comp σ (l + lamS S)]
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [sum_lamS_eq_card, sum_lamS_eq_card, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.filter_mem_eq_inter, Finset.univ_inter, hS, card_initSeg]

theorem defect_add (a b : Fin n → ℤ) : defect (a + b) = defect a + defect b := by
  rw [defect, defect, defect, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [tailSum_add]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem antitone_lamS_initSeg {r : ℕ} (hr : r ≤ n) : Antitone (lamS (initSeg hr)) := by
  intro i j hij
  have := Fin.le_def.1 hij
  simp only [lamS_apply, mem_initSeg]
  split_ifs <;> omega

theorem defect_lamS_initSeg_pos {r : ℕ} (hr : r < n) (hr0 : 0 < r) :
    0 < defect (lamS (initSeg hr.le)) := by
  refine Finset.sum_pos' (fun m _ => ?_) ⟨⟨1, by omega⟩, Finset.mem_univ _, ?_⟩
  · have := mul_tailSum_le (antitone_lamS_initSeg hr.le) (Nat.lt_succ_iff.1 m.2)
    linarith
  · have hsum : ∑ i, lamS (initSeg hr.le) i = r := by
      rw [sum_lamS_eq_card, Finset.filter_mem_eq_inter, Finset.univ_inter, card_initSeg]
    have htail : tailSum (lamS (initSeg hr.le)) (Nat.lt_succ_iff.1 (⟨1, by omega⟩ : Fin (n + 1)).2)
        = 0 := by
      rw [tailSum_eq_sum_tailSet, sum_lamS_eq_card]
      norm_cast
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i hi
      rw [mem_tailSet] at hi
      rw [mem_initSeg]
      simp only at hi
      omega
    rw [hsum, htail]
    simp only [Nat.cast_one, one_mul, mul_zero, sub_zero]
    exact_mod_cast hr0

theorem eq_zero_of_recursion (κ : Finset (Fin n) → ℝ) (hκ : ∀ S, 0 < κ S) (E : ℕ → ℂ)
    (hE : E n ≠ 0) (f : (Fin n → ℤ) → ℂ)
    (hrec : ∀ l : Fin n → ℤ, Antitone l → ∀ r ≤ n,
      E r * f l = ∑ S ∈ Finset.univ.powersetCard r, (κ S : ℂ) * f (l + lamS S))
    (hsort : ∀ l : Fin n → ℤ, Antitone l → ∀ S : Finset (Fin n),
      f (l + lamS S) = 0 ∨ ∃ σ : Equiv.Perm (Fin n), Antitone ((l + lamS S) ∘ σ) ∧
        f (l + lamS S) = f ((l + lamS S) ∘ σ))
    (h0 : f 0 = 0) : ∀ l : Fin n → ℤ, Antitone l → f l = 0 := by

  have hconst : ∀ c : ℤ, f (fun _ => c) = 0 := by
    have hstep : ∀ c : ℤ, E n * f (fun _ => c) = (κ Finset.univ : ℂ) * f (fun _ => c + 1) := by
      intro c
      have := hrec (fun _ => c) (fun _ _ _ => le_rfl) n le_rfl
      have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
        simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
      rw [this, hp, Finset.sum_singleton]
      congr 2
      funext i
      simp [lamS_apply]
    have hκu : (κ Finset.univ : ℂ) ≠ 0 := by exact_mod_cast (hκ _).ne'
    intro c
    induction c using Int.induction_on with
    | zero => exact h0
    | succ c ih =>
      have := hstep c
      rw [ih, mul_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hκu
    | pred c ih =>
      have := hstep (-(c : ℤ) - 1)
      rw [show -(c : ℤ) - 1 + 1 = -c by ring, ih, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hE

  suffices key : ∀ d : ℕ, ∀ ν : Fin n → ℤ, Antitone ν → (defect ν).toNat = d → f ν = 0 from
    fun ν hν => key _ ν hν rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro ν hν hd
    by_cases hc : ∀ i j, ν i = ν j
    · rcases n.eq_zero_or_pos with hn | hn
      · subst hn
        rw [show ν = 0 from funext fun i => i.elim0]
        exact h0
      · have : ν = fun _ => ν ⟨0, hn⟩ := funext fun i => hc i _
        rw [this]
        exact hconst _
    push Not at hc
    have hn : 0 < n := by
      obtain ⟨i, -, -⟩ := hc
      exact Fin.pos i
    set i0 : Fin n := ⟨0, hn⟩
    have hex : ∃ k, ∃ hk : k < n, ν ⟨k, hk⟩ ≠ ν i0 := by
      obtain ⟨i, j, hij⟩ := hc
      by_cases hi : ν i = ν i0
      · exact ⟨j, j.2, fun h => hij (hi.trans h.symm)⟩
      · exact ⟨i, i.2, hi⟩
    classical
    obtain ⟨r, hrn, hr0, hbefore, hrν⟩ : ∃ r, ∃ hrn : r < n, 0 < r ∧
        (∀ i : Fin n, (i : ℕ) < r → ν i = ν i0) ∧ ν ⟨r, hrn⟩ ≠ ν i0 := by
      obtain ⟨hrn, hrν⟩ := Nat.find_spec hex
      refine ⟨Nat.find hex, hrn, ?_, fun i hi => ?_, hrν⟩
      · by_contra h
        apply hrν
        congr 1
        exact Fin.ext (by simp only [i0]; omega)
      · have := Nat.find_min hex hi
        push Not at this
        exact this i.2
    obtain ⟨T, hT⟩ : ∃ T, T = initSeg hrn.le := ⟨_, rfl⟩
    obtain ⟨l, hl_def⟩ : ∃ l, l = ν - lamS T := ⟨_, rfl⟩
    have hνl : ν = l + lamS T := by rw [hl_def]; abel
    have hνr : ν ⟨r, hrn⟩ < ν i0 := lt_of_le_of_ne (hν (Fin.le_def.2 (Nat.zero_le _))) hrν
    have hl : Antitone l := by
      intro i j hij
      have hij' := Fin.le_def.1 hij
      rw [hl_def]
      simp only [Pi.sub_apply, lamS_apply, hT, mem_initSeg]
      have := hν hij
      by_cases hi : (i : ℕ) < r <;> by_cases hj : (j : ℕ) < r <;> simp only [hi, hj, if_true, if_false]
      · have := hbefore i hi
        have := hbefore j hj
        linarith
      · have hi' := hbefore i hi
        have hj' : ν j ≤ ν ⟨r, hrn⟩ := hν (Fin.le_def.2 (by simp only; omega))
        linarith
      · omega
      · linarith
    have hdef : defect ν = defect l + defect (lamS T) := by rw [hνl, defect_add]
    have hpos := defect_lamS_initSeg_pos hrn hr0
    rw [← hT] at hpos
    have hl0 : f l = 0 := by
      refine ih (defect l).toNat ?_ l hl rfl
      have := defect_nonneg hl
      omega
    have hterm : ∀ S ∈ Finset.univ.powersetCard r, f (l + lamS S) = 0 ∨ f (l + lamS S) = f ν := by
      intro S hS
      have hSr := (Finset.mem_powersetCard.1 hS).2
      rcases hsort l hl S with h | ⟨σ, hσ, hfσ⟩
      · exact Or.inl h
      · have hdom : DomLE ((l + lamS S) ∘ σ) ν := by
          rw [hνl, hT]
          exact domLE_rearrangement hl hrn.le hSr σ
        by_cases heq : (l + lamS S) ∘ σ = ν
        · exact Or.inr (hfσ.trans (by rw [heq]))
        · left
          rw [hfσ]
          have hlt := defect_lt hdom heq
          have hnn := defect_nonneg hσ
          exact ih _ (by omega) _ hσ rfl
    by_contra hfν
    have hsum := hrec l hl r hrn.le
    rw [hl0, mul_zero] at hsum
    have hsplit : ∑ S ∈ Finset.univ.powersetCard r, (κ S : ℂ) * f (l + lamS S) =
        (∑ S ∈ (Finset.univ.powersetCard r).filter (fun S => f (l + lamS S) = f ν), (κ S : ℂ)) *
          f ν := by
      rw [Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun S hS => ?_
      split_ifs with h
      · rw [h]
      · rw [(hterm S hS).resolve_right h, mul_zero]
    have hTmem : T ∈ (Finset.univ.powersetCard r).filter (fun S => f (l + lamS S) = f ν) := by
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, by rw [hT, card_initSeg]⟩, by rw [← hνl]⟩
    have hκsum : (0 : ℝ) <
        ∑ S ∈ (Finset.univ.powersetCard r).filter (fun S => f (l + lamS S) = f ν), κ S :=
      Finset.sum_pos (fun S _ => hκ S) ⟨T, hTmem⟩
    rw [hsplit] at hsum
    have hne : (∑ S ∈ (Finset.univ.powersetCard r).filter (fun S => f (l + lamS S) = f ν),
        (κ S : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_sum]
      exact_mod_cast hκsum.ne'
    exact hfν ((mul_eq_zero.1 hsum.symm).resolve_left hne)

end Spherical

end GroundTheory.Automorphic

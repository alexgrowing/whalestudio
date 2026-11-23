import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace KTy

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

abbrev Bx (nu : ι → Fin n → ℕ) : Type := Σ τ : ι, Σ i : Fin n, Fin (nu τ i)

abbrev Pr (H : Finset ι) (n : ℕ) : Type := Σ _ : H, Σ i : Fin n, Fin i.val

def eB (nu : ι → Fin n → ℕ) : Fin (Fintype.card (Bx nu)) ≃ Bx nu := (Fintype.equivFin _).symm

def eP (H : Finset ι) (n : ℕ) : Fin (Fintype.card (Pr H n)) ≃ Pr H n := (Fintype.equivFin _).symm

section
variable (nu : ι → Fin n → ℕ) (H : Finset ι)

theorem card_filter_comp {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → Prop) [DecidablePred f] :
    (Finset.univ.filter fun a => f (e a)).card = (Finset.univ.filter f).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp e (fun b => if f b then 1 else 0)

theorem card_filter_sum {α β : Type} [Fintype α] [Fintype β] (f : α ⊕ β → Prop) [DecidablePred f] :
    (Finset.univ.filter f).card =
      (Finset.univ.filter fun a => f (.inl a)).card + (Finset.univ.filter fun b => f (.inr b)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]

def labQ (p : Fin (Fintype.card (Bx nu))) : ι := (eB nu p).1

def bQ (p : Fin (Fintype.card (Bx nu))) : Fin n := (eB nu p).2.1

def colQ (p : Fin (Fintype.card (Bx nu))) : ℕ := Nat.pair (Fintype.equivFin ι (eB nu p).1) (eB nu p).2.2

def tl (k : Fin (Fintype.card (Pr H n))) : ι := (eP H n k).1

def rI (k : Fin (Fintype.card (Pr H n))) : Fin n := (eP H n k).2.1

def cI (k : Fin (Fintype.card (Pr H n))) : Fin n :=
  ⟨(eP H n k).2.2, lt_trans (eP H n k).2.2.isLt (eP H n k).2.1.isLt⟩

abbrev Pos : Type := Fin (Fintype.card (Bx nu)) ⊕ (Fin (Fintype.card (Pr H n)) ⊕ Fin (Fintype.card (Pr H n)))

abbrev Col (ι : Type) (n : ℕ) : Type := ℕ ⊕ ((ι × Fin n) ⊕ (ι × Fin n))

def colF : Pos nu H → Col ι n
  | .inl p => .inl (colQ nu p)
  | .inr (.inl k) => .inr (.inl (tl H k, cI H k))
  | .inr (.inr k) => .inr (.inr (tl H k, rI H k))

def bF : Pos nu H → Fin n
  | .inl p => bQ nu p
  | .inr (.inl k) => rI H k
  | .inr (.inr k) => Fin.rev (cI H k)

theorem bx_ext {x y : Bx nu} (h1 : x.1 = y.1) (h2 : x.2.1 = y.2.1) (h3 : (x.2.2 : ℕ) = y.2.2) : x = y := by
  obtain ⟨τ, i, c⟩ := x
  obtain ⟨τ', i', c'⟩ := y
  dsimp only at h1 h2 h3
  subst h1 h2
  rw [Fin.ext h3]

theorem pr_ext {x y : Pr H n} (h1 : (x.1 : ι) = y.1) (h2 : x.2.1 = y.2.1) (h3 : (x.2.2 : ℕ) = y.2.2) : x = y := by
  obtain ⟨⟨τ, hτ⟩, i, c⟩ := x
  obtain ⟨⟨τ', hτ'⟩, i', c'⟩ := y
  dsimp only at h1 h2 h3
  subst h1 h2
  rw [Fin.ext h3]

theorem colF_lab (bar : ι → ι) (p p' : Pos nu H) (h : colF nu H p = colF nu H p') :
    lab3 bar (labQ nu) (tl H) p = lab3 bar (labQ nu) (tl H) p' := by
  rcases p with p | k | k <;> rcases p' with p' | k' | k' <;> simp [colF, lab3, colQ, Nat.pair_eq_pair] at h ⊢
  all_goals first | exact h.1 | rw [h.1] | exact (Fintype.equivFin ι).injective (Fin.ext h.1)

theorem isTabQ (hm : ∀ τ, Monotone (nu τ)) : IsTab (colQ nu) (bQ nu) := by
  refine ⟨fun p q h hb => ?_, fun p i hi => ?_⟩
  · simp only [colQ, Nat.pair_eq_pair] at h
    exact (eB nu).injective (bx_ext nu ((Fintype.equivFin ι).injective (Fin.ext h.1)) hb h.2)
  · obtain ⟨q, hq⟩ := (eB nu).surjective
      ⟨(eB nu p).1, i, ⟨(eB nu p).2.2, lt_of_lt_of_le (eB nu p).2.2.isLt (hm _ hi.le)⟩⟩
    refine ⟨q, ?_, ?_⟩ <;> simp only [colQ, bQ] <;> rw [hq]

theorem isTabF (hm : ∀ τ, Monotone (nu τ)) : IsTab (colF nu H) (bF nu H) := by
  have hQ := isTabQ nu hm
  refine ⟨fun p q h hb => ?_, fun p i hi => ?_⟩
  · rcases p with p | k | k <;> rcases q with q | k' | k' <;> simp [colF, bF] at h hb ⊢
    · exact hQ.1 p q h hb
    · exact (eP H n).injective (pr_ext H h.1 hb (congrArg Fin.val h.2))
    · exact (eP H n).injective (pr_ext H h.1 h.2 (congrArg Fin.val hb))
  · rcases p with p | k | k
    · obtain ⟨q, hq1, hq2⟩ := hQ.2 p i hi
      exact ⟨.inl q, by simp [colF, hq1], hq2⟩
    · have h0 : ((eP H n k).2.2 : ℕ) < i := by
        have := (eP H n k).2.2.isLt
        have h' : ((eP H n k).2.1 : ℕ) < i := hi
        omega
      obtain ⟨q, hq⟩ := (eP H n).surjective ⟨(eP H n k).1, i, ⟨(eP H n k).2.2, h0⟩⟩
      have hq1 : tl H q = tl H k := by show (eP H n q).1.1 = _; rw [hq]; rfl
      have hq2 : rI H q = i := by show (eP H n q).2.1 = _; rw [hq]
      have hq3 : cI H q = cI H k := Fin.ext (by show ((eP H n q).2.2 : ℕ) = _; rw [hq]; rfl)
      exact ⟨.inr (.inl q), by simp [colF, hq1, hq3], by simp [bF, hq2]⟩
    · have h0 : ((Fin.rev i : Fin n) : ℕ) < (eP H n k).2.1 := by
        have := (eP H n k).2.2.isLt
        have h' : ((Fin.rev (cI H k) : Fin n) : ℕ) < i := hi
        have := i.isLt
        simp only [Fin.val_rev, cI] at h' ⊢
        omega
      obtain ⟨q, hq⟩ := (eP H n).surjective ⟨(eP H n k).1, (eP H n k).2.1, ⟨(Fin.rev i : Fin n), h0⟩⟩
      have hq1 : tl H q = tl H k := by show (eP H n q).1.1 = _; rw [hq]; rfl
      have hq2 : rI H q = rI H k := by show (eP H n q).2.1 = _; rw [hq]; rfl
      have hq3 : cI H q = Fin.rev i := Fin.ext (by show ((eP H n q).2.2 : ℕ) = _; rw [hq])
      exact ⟨.inr (.inr q), by simp [colF, hq1, hq2], by simp [bF, hq3]⟩

theorem cntQ (τ : ι) (i : Fin n) : (Finset.univ.filter fun p => labQ nu p = τ ∧ bQ nu p = i).card = nu τ i := by
  refine (card_filter_comp (eB nu) (fun x => x.1 = τ ∧ x.2.1 = i)).trans ?_
  rw [Finset.card_filter, Fintype.sum_sigma]
  simp [Fintype.sum_sigma, ite_and]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem sumFin (j m : ℕ) : ∑ c : Fin j, (if (c : ℕ) = m then 1 else 0 : ℕ) = if m < j then 1 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun c => if c = m then 1 else 0) j]
  simp [Finset.sum_ite_eq']

theorem sumRange (n m : ℕ) : ∑ j ∈ Finset.range n, (if m < j then 1 else 0 : ℕ) = n - (m + 1) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; split_ifs <;> omega

theorem cnt1 (τ : ι) (i : Fin n) :
    (Finset.univ.filter fun k => tl H k = τ ∧ rI H k = i).card = if τ ∈ H then (i : ℕ) else 0 := by
  refine (card_filter_comp (eP H n) (fun x => (x.1 : ι) = τ ∧ x.2.1 = i)).trans ?_
  rw [Finset.card_filter, Fintype.sum_sigma]
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_congr rfl (g := fun x : H => if (x : ι) = τ then (i : ℕ) else 0) (fun x _ => ?_)]
  · rw [Finset.sum_coe_sort H (fun x => if x = τ then (i : ℕ) else 0), Finset.sum_ite_eq']
  · by_cases h : (x : ι) = τ
    · simp [h]
    · simp [h]

theorem cnt2 (bar : ι → ι) (hinv : ∀ τ, bar (bar τ) = τ) (τ : ι) (i : Fin n) :
    (Finset.univ.filter fun k => bar (tl H k) = τ ∧ Fin.rev (cI H k) = i).card = if bar τ ∈ H then (i : ℕ) else 0 := by
  have hc : ∀ k, (bar (tl H k) = τ ∧ Fin.rev (cI H k) = i) ↔
      ((eP H n k).1 : ι) = bar τ ∧ ((eP H n k).2.2 : ℕ) = (Fin.rev i : ℕ) := by
    intro k
    have e1 : bar (tl H k) = τ ↔ tl H k = bar τ := ⟨fun h => by rw [← h, hinv], fun h => by rw [h, hinv]⟩
    have e2 : Fin.rev (cI H k) = i ↔ cI H k = Fin.rev i :=
      ⟨fun h => by rw [← h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
    rw [e1, e2, Fin.ext_iff]
    rfl
  rw [Finset.filter_congr (fun k _ => hc k)]
  refine (card_filter_comp (eP H n) (fun x => (x.1 : ι) = bar τ ∧ (x.2.2 : ℕ) = (Fin.rev i : ℕ))).trans ?_
  rw [Finset.card_filter, Fintype.sum_sigma]
  simp only [Fintype.sum_sigma, ite_and]
  have hj : ∑ j : Fin n, (if (Fin.rev i : ℕ) < j then 1 else 0 : ℕ) = i := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if (Fin.rev i : ℕ) < j then 1 else 0) n, sumRange]
    simp only [Fin.val_rev]
    omega
  rw [Finset.sum_congr rfl (g := fun x : H => if (x : ι) = bar τ then (i : ℕ) else 0) (fun x _ => ?_)]
  · rw [Finset.sum_coe_sort H (fun x => if x = bar τ then (i : ℕ) else 0), Finset.sum_ite_eq']
  · by_cases h : (x : ι) = bar τ
    · simp only [h, if_true]
      simp only [sumFin, hj]
    · simp [h]

theorem cntF (bar : ι → ι) (hinv : ∀ τ, bar (bar τ) = τ) (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H) (τ : ι) (i : Fin n) :
    (Finset.univ.filter fun p => lab3 bar (labQ nu) (tl H) p = τ ∧ bF nu H p = i).card = nu τ i + i := by
  refine (card_filter_sum _).trans ?_
  refine (congrArg₂ (· + ·) (cntQ nu τ i)
    ((card_filter_sum _).trans (congrArg₂ (· + ·) (cnt1 H τ i) (cnt2 H bar hinv τ i)))).trans ?_
  by_cases h : τ ∈ H
  · have := (hH τ).1 h
    simp [h, this]
  · have : bar τ ∈ H := by
      by_contra h'
      exact h ((hH τ).2 h')
    simp [h, this]

end

theorem pm_mul_alt {P : Type} [Fintype P] [DecidableEq P] {M : Type} [AddCommGroup M] [Module ℂ M]
    (G : Finset (Equiv.Perm P)) (σ₀ : Equiv.Perm P) (h : ∀ σ, σ₀ * σ ∈ G ↔ σ ∈ G) :
    (pm σ₀ * alt G : Module.End ℂ (TV n M P)) = ((Equiv.Perm.sign σ₀ : ℤ) : ℂ) • alt G := by
  unfold alt
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_nbij' (fun σ => σ₀ * σ) (fun σ => σ₀⁻¹ * σ) (fun σ hσ => (h σ).2 hσ)
    (fun σ hσ => (h _).1 (by simpa using hσ)) (fun σ _ => by simp) (fun σ _ => by simp) (fun σ _ => ?_)
  have e : ((Equiv.Perm.sign σ₀ : ℤ) : ℂ) * ((Equiv.Perm.sign σ₀ : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  rw [mul_smul_comm, ← pm_mul, smul_smul]
  congr 1
  rw [Equiv.Perm.sign_mul]
  push_cast
  linear_combination -(((Equiv.Perm.sign σ : ℤ) : ℂ)) * e

theorem alt_comm {P : Type} [Fintype P] [DecidableEq P] {M : Type} [AddCommGroup M] [Module ℂ M]
    (G : Finset (Equiv.Perm P)) (x : Module.End ℂ (TV n M P)) (h : ∀ σ ∈ G, Commute (pm σ) x) :
    Commute (alt G) x := by
  unfold alt
  exact Commute.sum_left _ _ _ fun σ hσ => (h σ hσ).smul_left _

theorem sort_data (l : ι → Fin n → ℤ) (hl : ∀ τ, Function.Injective (l τ)) :
    ∃ (s : ℤ) (w : ι → Equiv.Perm (Fin n)) (nu : ι → Fin n → ℕ),
      (∀ τ i, (nu τ i : ℤ) = s - l τ (w τ i) - i) ∧ ∀ τ, Monotone (nu τ) := by
  set s : ℤ := ∑ τ, ∑ k, |l τ k| with hs
  have hsl : ∀ τ k, 0 ≤ s - l τ k := by
    intro τ k
    have h1 : |l τ k| ≤ ∑ k', |l τ k'| :=
      Finset.single_le_sum (f := fun k' => |l τ k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h2 : ∑ k', |l τ k'| ≤ s :=
      Finset.single_le_sum (f := fun τ' => ∑ k', |l τ' k'|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ)
    have h3 := le_abs_self (l τ k)
    linarith
  let w : ι → Equiv.Perm (Fin n) := fun τ => Tuple.sort (fun k => -l τ k)
  have hsm : ∀ τ, StrictMono (fun i => s - l τ (w τ i)) := by
    intro τ
    have h1 : Monotone ((fun k => -l τ k) ∘ w τ) := Tuple.monotone_sort _
    apply Monotone.strictMono_of_injective
    · intro a b hab
      have := h1 hab
      simp only [Function.comp_apply] at this
      linarith
    · intro a b hab
      simp only at hab
      exact (w τ).injective (hl τ (by linarith))
  have gap : ∀ τ (d : ℕ) (i j : Fin n), (j : ℕ) = i + d → s - l τ (w τ i) + d ≤ s - l τ (w τ j) := by
    intro τ d
    induction d with
    | zero =>
      intro i j h
      obtain rfl : j = i := Fin.ext (by omega)
      simp
    | succ d ih =>
      intro i j h
      have hj : (i : ℕ) + d < n := by have := j.isLt; omega
      have h1 := ih i ⟨i + d, hj⟩ rfl
      have h2 := hsm τ (show (⟨i + d, hj⟩ : Fin n) < j from by show (i : ℕ) + d < j; omega)
      simp only at h2
      push_cast
      linarith
  refine ⟨s, w, fun τ i => (s - l τ (w τ i) - i).toNat, fun τ i => ?_, fun τ a b hab => ?_⟩
  · have h1 := gap τ i ⟨0, i.pos⟩ i (by simp)
    have h2 := hsl τ (w τ ⟨0, i.pos⟩)
    simp only
    rw [Int.toNat_of_nonneg (by linarith)]
  · simp only
    have hab' : (a : ℕ) ≤ b := hab
    have h1 := gap τ ((b : ℕ) - a) a b (by omega)
    have e : (((b : ℕ) - (a : ℕ) : ℕ) : ℤ) = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) := by omega
    apply Int.toNat_le_toNat
    linarith

theorem half (bar : ι → ι) (hinv : ∀ τ, bar (bar τ) = τ) (hne : ∀ τ, bar τ ≠ τ) :
    ∃ H : Finset ι, ∀ τ, τ ∈ H ↔ bar τ ∉ H := by
  refine ⟨Finset.univ.filter fun τ => Fintype.equivFin ι τ < Fintype.equivFin ι (bar τ), fun τ => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hinv, not_lt]
  have : Fintype.equivFin ι τ ≠ Fintype.equivFin ι (bar τ) := fun h => hne τ ((Fintype.equivFin ι).injective h).symm
  exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h this⟩

end KTy

end PositivityTheory.Rg.Cz

end

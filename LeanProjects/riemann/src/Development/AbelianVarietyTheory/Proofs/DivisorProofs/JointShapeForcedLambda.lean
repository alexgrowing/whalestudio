import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ShapeForced
open Formalism.BasicNotions.TH

theorem getD_replicate_append (m k : ℕ) (u w : ℚ) (i : ℕ) :
    (List.replicate m u ++ List.replicate k w).getD i 0 = if i < m then u else if i < m + k then w else 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : i < m
  · rw [List.getElem?_append_left (by simpa using h1)]; simp [h1]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, h1, if_false, List.getElem?_replicate]
    by_cases h2 : i < m + k
    · simp [h2, show i - m < k by omega]
    · simp [h2, show ¬ i - m < k by omega]

theorem all_eq_of_getD {L : List ℚ} {n : ℕ} {v : ℚ} (hn : L.length = n) (h : ∀ i < n, L.getD i 0 = v) :
    ∀ x ∈ L, x = v := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have := h i (hn ▸ hi)
  rwa [List.getD_eq_getElem _ _ hi] at this

theorem pad_length (a b : List ℤ) (k : ℕ) : (pad a k b).length = a.length + k + b.length := by
  simp [pad]; omega

theorem forced (a b : List ℤ) (n : ℕ) (v : ℚ) (hlen : a.length + b.length ≤ n)
    (h : ∀ i < n, (pad a (n - a.length - b.length) b).getD i 0 = v) :
    (∀ x ∈ a, (x : ℚ) = v) ∧ (∀ x ∈ b, (x : ℚ) = v) ∧ (0 < n - a.length - b.length → (0 : ℚ) = v) := by
  have hall := all_eq_of_getD (by rw [pad_length]; omega) h
  refine ⟨fun x hx => hall _ ?_, fun x hx => hall _ ?_, fun hk => hall _ ?_⟩
  · simp only [pad, List.map_append, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
  · simp only [pad, List.map_append, List.mem_append, List.mem_map]; exact Or.inr ⟨x, hx, rfl⟩
  · simp only [pad, List.map_append, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨0, List.mem_replicate.mpr ⟨by omega, rfl⟩, by simp⟩)

theorem cast_pos_of {l : List ℤ} {v : ℚ} (hv : 0 < v) (hl : ∀ x ∈ l, x < 0) (he : ∀ x ∈ l, (x : ℚ) = v) : l = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have h1 := he x hx
  have h2 : (x : ℚ) < 0 := by exact_mod_cast hl x hx
  linarith

theorem cast_neg_of {l : List ℤ} {v : ℚ} (hv : v < 0) (hl : ∀ x ∈ l, 0 < x) (he : ∀ x ∈ l, (x : ℚ) = v) : l = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have h1 := he x hx
  have h2 : (0 : ℚ) < x := by exact_mod_cast hl x hx
  linarith

theorem map_rep {l : List ℤ} {n : ℕ} {v : ℚ} (hn : l.length = n) (he : ∀ x ∈ l, (x : ℚ) = v) :
    l.map (fun x : ℤ => (x : ℚ)) = List.replicate n v := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [hn], ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact he x hx

end GlobalTheory.ShapeForced

open Formalism.BasicNotions.TH GlobalTheory.ShapeForced in
theorem GlobalTheory.RealLift.jointShape_halfKappa : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → (∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => (κ : ℚ) / 2) μ' → μ' = GlobalTheory.RealLift.lam P Q R S κ) ∧ ∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P' Q' R S (fun _ => -((κ : ℚ) / 2)) μ' → (fun c => μ' c + (κ : ℚ) / 2) = GlobalTheory.RealLift.lam P Q R S κ := by
  intro P Q P' Q' R S κ hN
  obtain ⟨hR, hS, hSP, hSQ', -, -, hlt⟩ := hN
  have hltQ : (R : ℚ) + S < κ := by exact_mod_cast hlt
  constructor
  · rintro μ' ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, had, hcb, h1, h2⟩
    have pA : 0 < (κ : ℚ) / 2 - cPair R S := by unfold cPair; linarith
    have pC : 0 < (κ : ℚ) / 2 + cPair R S := by unfold cPair; linarith
    have hA : ∀ i < P, (pad a (P - a.length - b.length) b).getD i 0 = (κ : ℚ) / 2 - cPair R S := by
      intro i hi
      have := congrFun h1 (.inl ⟨i, hi⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    have hC : ∀ j < Q, (pad c (Q - c.length - d.length) d).getD j 0 = (κ : ℚ) / 2 + cPair R S := by
      intro j hj
      have := congrFun h1 (.inr ⟨j, hj⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    obtain ⟨haA, hbA, hkA⟩ := forced a b P _ hab hA
    obtain ⟨hcC, hdC, hkC⟩ := forced c d Q _ hcd hC
    have hb0 := cast_pos_of pA hb hbA
    have hd0 := cast_pos_of pC hd hdC
    subst hb0 hd0
    have hal : a.length = P := by
      by_contra hne
      have := hkA (by simp; omega)
      linarith
    have hcl : c.length = Q := by
      by_contra hne
      have := hkC (by simp; omega)
      linarith
    have hamap := map_rep hal haA
    have hcmap := map_rep hcl hcC
    funext x
    have := congrFun h2 x
    rcases x with ⟨i, hi⟩ | ⟨j, hj⟩
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hamap, List.map_nil, List.append_nil,
        getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      split_ifs at this ⊢ <;> first | linarith | omega
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hcmap, List.map_nil, List.append_nil,
        getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      split_ifs at this ⊢ <;> first | linarith | omega
  · rintro μ' ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, had, hcb, h1, h2⟩
    have pB : -((κ : ℚ) / 2) - cPair R S < 0 := by unfold cPair; linarith
    have pD : -((κ : ℚ) / 2) + cPair R S < 0 := by unfold cPair; linarith
    have hB : ∀ i < P', (pad a (P' - a.length - b.length) b).getD i 0 = -((κ : ℚ) / 2) - cPair R S := by
      intro i hi
      have := congrFun h1 (.inl ⟨i, hi⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    have hD : ∀ j < Q', (pad c (Q' - c.length - d.length) d).getD j 0 = -((κ : ℚ) / 2) + cPair R S := by
      intro j hj
      have := congrFun h1 (.inr ⟨j, hj⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    obtain ⟨haB, hbB, hkB⟩ := forced a b P' _ hab hB
    obtain ⟨hcD, hdD, hkD⟩ := forced c d Q' _ hcd hD
    have ha0 := cast_neg_of pB ha haB
    have hc0 := cast_neg_of pD hc hcD
    subst ha0 hc0
    have hbl : b.length = P' := by
      by_contra hne
      have := hkB (by simp at hab ⊢; omega)
      linarith
    have hdl : d.length = Q' := by
      by_contra hne
      have := hkD (by simp at hcd ⊢; omega)
      linarith
    have hbmap := map_rep hbl hbB
    have hdmap := map_rep hdl hdD
    funext x
    have := congrFun h2 x
    rcases x with ⟨i, hi⟩ | ⟨j, hj⟩
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hdmap, List.map_nil, List.nil_append,
        List.length_nil, getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      subst hR hS
      unfold cPair at this ⊢
      push_cast at this ⊢
      split_ifs at this ⊢ <;> first | linarith | omega
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hbmap, List.map_nil, List.nil_append,
        List.length_nil, getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      subst hR hS
      unfold cPair at this ⊢
      push_cast at this ⊢
      rw [hbl] at this
      by_cases hjQ : j < Q
      · rw [if_pos (by omega)] at this
        rw [if_pos hjQ]
        linarith
      · rw [if_neg (by omega), if_pos (by omega)] at this
        rw [if_neg hjQ]
        linarith

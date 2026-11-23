import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem pad_all (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    ∀ v ∈ a ++ List.replicate (p - a.length - b.length) 0 ++ b, v = z := by
  intro v hv
  have hlen : (a ++ List.replicate (p - a.length - b.length) 0 ++ b).length = p := by
    simp only [List.length_append, List.length_replicate]
    omega
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have h1 := h ⟨i, hlen ▸ hi⟩
  simp only [pad, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some] at h1
  exact_mod_cast h1

theorem pad_pos (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ) (hz : 0 < z)
    (hb : ∀ v ∈ b, v < 0)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    a = List.replicate p z ∧ b = [] := by
  have hall := pad_all a b p hl z h
  have hb' : b = [] := by
    rcases b with _ | ⟨v, b⟩
    · rfl
    · exfalso
      have h1 := hall v (by simp)
      have h2 := hb v (by simp)
      omega
  subst hb'
  have hk : p - a.length - ([] : List ℤ).length = 0 := by
    by_contra hne
    have := hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2
      (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))
    omega
  refine ⟨List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩, rfl⟩
  simp only [List.length_nil] at hk hl
  omega

theorem pad_neg (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ) (hz : z < 0)
    (ha : ∀ v ∈ a, 0 < v)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    a = [] ∧ b = List.replicate p z := by
  have hall := pad_all a b p hl z h
  have ha' : a = [] := by
    rcases a with _ | ⟨v, a⟩
    · rfl
    · exfalso
      have h1 := hall v (by simp)
      have h2 := ha v (by simp)
      omega
  subst ha'
  have hk : p - ([] : List ℤ).length - b.length = 0 := by
    by_contra hne
    have := hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2
      (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))
    omega
  refine ⟨rfl, List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩⟩
  simp only [List.length_nil] at hk hl
  omega

theorem getD_pad_left (p k i : ℕ) (z : ℤ) :
    (pad (List.replicate p z) k []).getD i 0 = if i < p then (z : ℚ) else 0 := by
  simp only [pad, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  split_ifs <;> simp_all <;> omega

theorem getD_pad_right (q r i : ℕ) (z : ℤ) (hq : q ≤ r) (hi : i < r) :
    (pad [] (r - q) (List.replicate q z)).getD i 0 = if r ≤ i + q then (z : ℚ) else 0 := by
  simp only [pad, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  split_ifs <;> simp_all <;> omega

theorem shift_pos_eq (p q r s n m : ℕ) :
    shiftNu (cPair p q) (laPos p q r s n m) =
      ofBlocks (pad (List.replicate p (n : ℤ)) (r - p) []) (pad (List.replicate q (m : ℤ)) (s - q) []) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring

theorem shift_neg_eq (p q r s n m : ℕ) (hq : q ≤ r) (hp : p ≤ s) :
    shiftNu (cPair p q) (laNeg p q r s n m) =
      ofBlocks (pad [] (r - q) (List.replicate q (-(n : ℤ)))) (pad [] (s - p) (List.replicate p (-(m : ℤ)))) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right q r k _ hq k.isLt]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right p s l _ hp l.isLt]
    split_ifs <;> push_cast <;> ring

theorem shiftNu_inj {r s : ℕ} (c : ℚ) {μ ν : Ix r s → ℚ} (h : shiftNu c μ = shiftNu c ν) : μ = ν := by
  funext x
  have := congrFun h x
  rcases x with k | l <;> simp only [shiftNu] at this <;> linarith

theorem shape_pos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = n + cPair r s) (h2 : c0 = m - cPair r s) :
    JointShape p q r s (fun _ => c0) (laPos p q r s n m) ∧
      ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = laPos p q r s n m := by
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hm' : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  refine ⟨⟨List.replicate p (n : ℤ), [], List.replicate q (m : ℤ), [], ?_⟩, ?_⟩
  · refine ⟨fun v hv => (List.eq_of_mem_replicate hv) ▸ hn', fun v hv => (List.eq_of_mem_replicate hv) ▸ hm',
      fun v hv => by simp at hv, fun v hv => by simp at hv,
      List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil,
      List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hp
    · simpa using hq
    · funext x
      rcases x with i | j
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.zero_sub, getD_pad_left, i.isLt, if_true]
        rw [h1]; push_cast; ring
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.zero_sub, getD_pad_left, j.isLt, if_true]
        rw [h2]; push_cast; ring
    · simp only [List.length_replicate, List.length_nil, Nat.sub_zero]
      exact shift_pos_eq p q r s n m
  · rintro ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩
    have hA := pad_pos a b p hab (n : ℤ) hn' hb (fun i => by
      have hx := congrFun hs1 (Sum.inl i)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h1]; push_cast; ring)
    have hC := pad_pos c d q hcd (m : ℤ) hm' hd (fun j => by
      have hx := congrFun hs1 (Sum.inr j)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h2]; push_cast; ring)
    obtain ⟨rfl, rfl⟩ := hA
    obtain ⟨rfl, rfl⟩ := hC
    apply shiftNu_inj (cPair p q)
    rw [hs2, shift_pos_eq]
    simp only [List.length_replicate, List.length_nil, Nat.sub_zero]

theorem shape_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s) :
    JointShape p q r s (fun _ => c0) (laNeg p q r s n m) ∧
      ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = laNeg p q r s n m := by
  have hn' : (-(n : ℤ)) < 0 := by
    have : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
    omega
  have hm' : (-(m : ℤ)) < 0 := by
    have : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
    omega
  refine ⟨⟨[], List.replicate p (-(m : ℤ)), [], List.replicate q (-(n : ℤ)), ?_⟩, ?_⟩
  · refine ⟨fun v hv => by simp at hv, fun v hv => by simp at hv,
      fun v hv => (List.eq_of_mem_replicate hv) ▸ hm', fun v hv => (List.eq_of_mem_replicate hv) ▸ hn',
      List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl),
      List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hq
    · simpa using hp
    · funext x
      rcases x with i | j
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.sub_zero]
        have e := getD_pad_right p p i (-(m : ℤ)) le_rfl i.isLt
        rw [Nat.sub_self, if_pos (by omega)] at e
        rw [e, h1]; push_cast; ring
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.sub_zero]
        have e := getD_pad_right q q j (-(n : ℤ)) le_rfl j.isLt
        rw [Nat.sub_self, if_pos (by omega)] at e
        rw [e, h2]; push_cast; ring
    · simp only [List.length_replicate, List.length_nil, Nat.sub_zero]
      exact shift_neg_eq p q r s n m hq hp
  · rintro ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩
    have hA := pad_neg a b p hab (-(m : ℤ)) hm' ha (fun i => by
      have hx := congrFun hs1 (Sum.inl i)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h1]; push_cast; ring)
    have hC := pad_neg c d q hcd (-(n : ℤ)) hn' hc (fun j => by
      have hx := congrFun hs1 (Sum.inr j)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h2]; push_cast; ring)
    obtain ⟨rfl, rfl⟩ := hA
    obtain ⟨rfl, rfl⟩ := hC
    apply shiftNu_inj (cPair p q)
    rw [hs2, shift_neg_eq p q r s n m hq hp]
    simp only [List.length_replicate, List.length_nil, Nat.sub_zero]

end PositivityTheory.KReal

end

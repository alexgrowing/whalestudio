import Mathlib

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial IntermediateField

theorem fl_step {F E : Type*} [Field F] [Field E] [Algebra F E] (p : ℕ) [hp : Fact p.Prime]
    [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E))
    (L : IntermediateField F E) {x : E} (hx : x ∉ L) :
    finrank L (adjoin L {x}) = p := by
  obtain ⟨a, ha⟩ := h x
  have hxp : x ^ p ∈ L := ha ▸ L.algebraMap_mem a
  set b : L := ⟨x ^ p, hxp⟩ with hb
  have hirr : Irreducible (X ^ p - C b) := by
    apply X_pow_sub_C_irreducible_of_prime hp.out
    intro y hy
    apply hx
    have h1 : (y : E) ^ p = x ^ p := by
      have := congrArg (fun z : L => (z : E)) hy
      simpa [hb] using this
    have h2 : (y : E) = x := frobenius_inj E p (by simpa [frobenius_def] using h1)
    exact h2 ▸ y.2
  have haev : aeval x (X ^ p - C b) = 0 := by
    simp [hb]
  have hmon : (X ^ p - C b).Monic := monic_X_pow_sub_C _ hp.out.ne_zero
  have hmin : X ^ p - C b = minpoly L x := minpoly.eq_of_irreducible_of_monic hirr haev hmon
  have hint : IsIntegral L x := ⟨X ^ p - C b, hmon, by simpa [aeval_def] using haev⟩
  rw [adjoin.finrank hint, ← hmin, natDegree_X_pow_sub_C]

theorem fl_greedy {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [hp : Fact p.Prime] [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E)) :
    ∀ (N : ℕ) (L : IntermediateField F E), L.relfinrank ⊤ = N →
      ∃ n, L.relfinrank ⊤ = p ^ n ∧ ∃ α : Fin n → E, L ⊔ adjoin F (Set.range α) = ⊤ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro L hL
  by_cases hT : L = ⊤
  · subst hT
    exact ⟨0, by simp [relfinrank_self], Fin.elim0, top_sup_eq _⟩
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hT)
  set L' : IntermediateField F E := (adjoin L ({x} : Set E)).restrictScalars F with hL'
  have hsup : L' = L ⊔ adjoin F ({x} : Set E) := by rw [hL', restrictScalars_adjoin_eq_sup]
  have hle : L ≤ L' := hsup ▸ le_sup_left
  have hdeg : L.relfinrank L' = p := by
    rw [relfinrank_eq_finrank_of_le hle]
    have : extendScalars hle = adjoin L ({x} : Set E) :=
      restrictScalars_injective F (by rw [extendScalars_restrictScalars])
    rw [this, fl_step p h L hx]
  have hmul := relfinrank_mul_relfinrank hle (le_top : L' ≤ ⊤)
  have hpos : 0 < L.relfinrank ⊤ := by
    rw [relfinrank_top_right]; exact Module.finrank_pos
  have hlt : L'.relfinrank ⊤ < N := by
    rw [← hL, ← hmul, hdeg]
    have h2 := hp.out.two_le
    have : 0 < L'.relfinrank ⊤ := by
      rcases Nat.eq_zero_or_pos (L'.relfinrank ⊤) with h0 | h0
      · rw [← hmul, h0, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    nlinarith
  obtain ⟨m, hm, β, hβ⟩ := ih _ hlt L' rfl
  refine ⟨m + 1, ?_, Fin.cons x β, ?_⟩
  · rw [← hmul, hdeg, hm, pow_succ']
  · rw [Fin.range_cons, Set.insert_eq, adjoin_union, ← sup_assoc, ← hsup, hβ]

theorem fl_main {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [Fact p.Prime] [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E)) :
    ∃ n, finrank F E = p ^ n ∧ ∃ α : Fin n → E, adjoin F (Set.range α) = ⊤ := by
  obtain ⟨n, hn, α, hα⟩ := fl_greedy p h _ ⊥ rfl
  refine ⟨n, ?_, α, ?_⟩
  · rw [← hn, relfinrank_bot_left, finrank_top']
  · rwa [bot_sup_eq] at hα

def Pj (E : Type*) [Field E] (p : ℕ) [Fact p.Prime] [CharP E p] (j : ℕ) : Subfield E :=
  (iterateFrobenius E p j).fieldRange

section Frob

variable {E : Type*} [Field E] (p : ℕ) [hp : Fact p.Prime] [CharP E p]

theorem mem_Pj {j : ℕ} {y : E} : y ∈ Pj E p j ↔ ∃ x : E, x ^ p ^ j = y := by
  simp [Pj, RingHom.mem_fieldRange, iterateFrobenius_def]

theorem Pj_zero : Pj E p 0 = ⊤ :=
  eq_top_iff.2 fun y _ => (mem_Pj p).2 ⟨y, by simp⟩

theorem Pj_succ_le (j : ℕ) : Pj E p (j + 1) ≤ Pj E p j := by
  intro y hy
  obtain ⟨x, rfl⟩ := (mem_Pj p).1 hy
  exact (mem_Pj p).2 ⟨x ^ p, by rw [← pow_mul, pow_succ']⟩

theorem comp_iterateFrobenius (j : ℕ) :
    (iterateFrobenius E p j).comp (iterateFrobenius E p 1) = iterateFrobenius E p (j + 1) := by
  ext x
  simp only [RingHom.comp_apply, iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]

theorem map_Pj_one (j : ℕ) : (Pj E p 1).map (iterateFrobenius E p j) = Pj E p (j + 1) := by
  rw [Pj, RingHom.map_fieldRange, comp_iterateFrobenius, Pj]

theorem map_top_Pj (j : ℕ) : (⊤ : Subfield E).map (iterateFrobenius E p j) = Pj E p j :=
  (RingHom.fieldRange_eq_map _).symm

theorem relfinrank_Pj_succ (j : ℕ) :
    (Pj E p (j + 1)).relfinrank (Pj E p j) = (Pj E p 1).relfinrank ⊤ := by
  rw [← map_Pj_one p j, ← map_top_Pj p j, Subfield.relfinrank_map_map]

theorem relfinrank_Pj (j : ℕ) :
    (Pj E p j).relfinrank ⊤ = ((Pj E p 1).relfinrank ⊤) ^ j := by
  induction j with
  | zero => rw [pow_zero, Subfield.relfinrank_eq_one_iff, Pj_zero]
  | succ j ih =>
    rw [← Subfield.relfinrank_mul_relfinrank (Pj_succ_le p j) le_top, relfinrank_Pj_succ, ih,
      pow_succ']

theorem closure_Pj_eq_top {S : Set E} (hS : Subfield.closure ((Pj E p 1 : Set E) ∪ S) = ⊤)
    (j : ℕ) : Subfield.closure ((Pj E p j : Set E) ∪ S) = ⊤ := by
  have key : ∀ i, Pj E p i ≤ Subfield.closure ((Pj E p (i + 1) : Set E) ∪ S) := by
    intro i
    rw [← map_top_Pj p i, ← hS, Subfield.map_le_iff_le_comap, Subfield.closure_le]
    rintro y (hy | hy)
    · change y ∈ Pj E p 1 at hy
      obtain ⟨x, rfl⟩ := (mem_Pj p).1 hy
      rw [SetLike.mem_coe, Subfield.mem_comap]
      apply Subfield.subset_closure
      left
      exact (mem_Pj p).2 ⟨x, by rw [iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]⟩
    · rw [SetLike.mem_coe, Subfield.mem_comap, iterateFrobenius_def]
      exact pow_mem (Subfield.subset_closure (Set.mem_union_right _ hy) :
        y ∈ Subfield.closure ((Pj E p (i + 1) : Set E) ∪ S)) _
  induction j with
  | zero =>
    rw [Pj_zero]
    exact eq_top_iff.2 fun y _ => Subfield.subset_closure (Or.inl (Subfield.mem_top y))
  | succ j ih =>
    refine eq_top_iff.2 (ih ▸ Subfield.closure_le.2 (Set.union_subset (key j) ?_))
    exact fun y hy => Subfield.subset_closure (Or.inr hy)

theorem fl_frob (c : ℕ) (hc : 0 < c) (hfin : (Pj E p c).relfinrank ⊤ ≠ 0) :
    ∃ n, (Pj E p c).relfinrank ⊤ = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Subfield.closure ((Pj E p c : Set E) ∪ Set.range α) = ⊤ := by
  have h1 : (Pj E p 1).relfinrank ⊤ ≠ 0 := by
    intro h0
    apply hfin
    rw [relfinrank_Pj, h0, zero_pow hc.ne']
  haveI : FiniteDimensional (Pj E p 1) E :=
    Module.finite_of_finrank_pos (by rw [← Subfield.relfinrank_top_right]; exact Nat.pos_of_ne_zero h1)
  obtain ⟨n, hn, α, hα⟩ := fl_main (F := Pj E p 1) (E := E) p
    (fun x => ⟨⟨x ^ p, (mem_Pj p).2 ⟨x, by rw [pow_one]⟩⟩, rfl⟩)
  refine ⟨n, ?_, α, closure_Pj_eq_top p ?_ c⟩
  · rw [relfinrank_Pj, Subfield.relfinrank_top_right, hn, ← pow_mul, ← pow_mul, mul_comm]
  · have := congrArg IntermediateField.toSubfield hα
    rw [adjoin_toSubfield, top_toSubfield] at this
    have hr : Set.range (algebraMap (Pj E p 1) E) = (Pj E p 1 : Set E) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact z.2
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    rwa [hr] at this

end Frob

end PositivityTheory.RgUd.TP.Desc.Piece.PSect

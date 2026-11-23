import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree

open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Cu.TorusWeightSpan

theorem span_mul {Γ K : Type} [Group Γ] [Field K] (r : Γ →* M4 K) (E : Subfield K) {x y : M4 K}
    (hx : x ∈ Submodule.span E (Set.range r)) (hy : y ∈ Submodule.span E (Set.range r)) :
    x * y ∈ Submodule.span E (Set.range r) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, rfl⟩ := ha
      obtain ⟨h, rfl⟩ := hb
      exact Submodule.subset_span ⟨g * h, map_mul r g h⟩
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add b c _ _ hb hc => rw [add_mul]; exact add_mem hb hc
  | smul c b _ hb => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hb

theorem span_trace {Γ K : Type} [Group Γ] [Field K] (r : Γ →* M4 K) (E : Subfield K)
    (ht : ∀ g, (r g).trace ∈ E) {x : M4 K} (hx : x ∈ Submodule.span E (Set.range r)) : x.trace ∈ E := by
  induction hx using Submodule.span_induction with
  | mem a ha => obtain ⟨g, rfl⟩ := ha; exact ht g
  | zero => simp
  | add b c _ _ hb hc => rw [Matrix.trace_add]; exact add_mem hb hc
  | smul c b _ hb => rw [Matrix.trace_smul]; exact mul_mem c.2 hb

theorem eii {Γ K : Type} [Group Γ] [Field K] (r : Γ →* M4 K) (E : Subfield K) (g0 : Γ)
    (hd : (r g0).IsDiag) (hne : ∀ i j, i ≠ j → r g0 i i ≠ r g0 j j) (hE : ∀ i, r g0 i i ∈ E) (i : Fin 4) :
    Matrix.single i i (1 : K) ∈ Submodule.span E (Set.range r) := by
  have h1 : (1 : M4 K) ∈ Submodule.span E (Set.range r) := Submodule.subset_span ⟨1, map_one r⟩
  have h0 : r g0 ∈ Submodule.span E (Set.range r) := Submodule.subset_span ⟨g0, rfl⟩
  have key : Matrix.diagonal (∏ j ∈ Finset.univ.erase i,
      (fun k => (r g0 i i - r g0 j j)⁻¹ * (r g0 k k - r g0 j j) : Fin 4 → K)) ∈ Submodule.span E (Set.range r) := by
    refine Finset.prod_induction _ (fun v : Fin 4 → K => Matrix.diagonal v ∈ Submodule.span E (Set.range r)) ?_ ?_ ?_
    · intro a b ha hb
      have := span_mul r E ha hb
      rwa [Matrix.diagonal_mul_diagonal] at this
    · exact h1
    · intro j _
      have := Submodule.smul_mem _ (⟨(r g0 i i - r g0 j j)⁻¹, inv_mem (sub_mem (hE i) (hE j))⟩ : E)
        (sub_mem h0 (Submodule.smul_mem _ (⟨r g0 j j, hE j⟩ : E) h1))
      convert this using 1
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [Subfield.smul_def]
      · simp [Subfield.smul_def, hab, hd hab]
  convert key using 1
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, Finset.prod_apply]
    by_cases hi : i = a
    · subst hi
      rw [Matrix.single_apply_same]
      symm
      refine Finset.prod_eq_one fun j hj => ?_
      exact inv_mul_cancel₀ (sub_ne_zero.2 (hne _ _ (Finset.ne_of_mem_erase hj).symm))
    · rw [Matrix.single_apply_of_row_ne hi]
      symm
      exact Finset.prod_eq_zero (i := a) (Finset.mem_erase.2 ⟨Ne.symm hi, Finset.mem_univ _⟩) (by simp)
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.single_apply_of_ne]
    rintro ⟨rfl, rfl⟩
    exact hab rfl

theorem wt_be : ∀ i j : Fin 4, wt i j = wBe → i = 1 ∧ j = 2 := by decide

theorem wt_mbe : ∀ i j : Fin 4, wt i j = -wBe → i = 2 ∧ j = 1 := by decide

theorem wt_th : ∀ i j : Fin 4, wt i j = wTh → i = 0 ∧ j = 3 := by decide

theorem wt_mth : ∀ i j : Fin 4, wt i j = -wTh → i = 3 ∧ j = 0 := by decide

theorem wt_off : ∀ i j : Fin 4, i ≠ j → wt i j ∈ UpperTheory.V.Cu.yY →
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) := by
  unfold UpperTheory.V.Cu.yY
  decide

end UpperTheory.V.Cu.TorusWeightSpan

open UpperTheory.V.Cu.TorusWeightSpan in
theorem UpperTheory.V.Cu.torusY : UpperTheory.V.Cu.TorusY := by
  intro Γ K _ _ r g0 hd hne hS hb hmb ht hmt
  have ent : ∀ (w : ℤ × ℤ) (a b : Fin 4), (∀ i j : Fin 4, wt i j = w → i = a ∧ j = b) → Ent r w →
      ∃ g, r g a b ≠ 0 := by
    rintro w a b hw ⟨g, i, j, hij, hg⟩
    obtain ⟨rfl, rfl⟩ := hw i j hij
    exact ⟨g, hg⟩
  obtain ⟨gs, hs⟩ := ent _ 0 3 wt_th ht
  obtain ⟨gt, hgt⟩ := ent _ 1 2 wt_be hb
  obtain ⟨g30, h30⟩ := ent _ 3 0 wt_mth hmt
  obtain ⟨g21, h21⟩ := ent _ 2 1 wt_mbe hmb
  refine ⟨r gs 0 3, r gt 1 2, fun E hsE htE htr hE => ?_⟩
  have he := eii r E g0 hd hne hE
  have hent : ∀ g i j, Matrix.single i j (r g i j) ∈ Submodule.span E (Set.range r) := by
    intro g i j
    have h1 := span_mul r E (span_mul r E (he i) (Submodule.subset_span ⟨g, rfl⟩)) (he j)
    rw [Matrix.single_mul_mul_single] at h1
    simpa using h1
  have hQE : ∀ (i j : Fin 4) (c : K), c ≠ 0 → c ∈ E → Matrix.single i j c ∈ Submodule.span E (Set.range r) →
      ∀ g, r g j i ∈ E := by
    intro i j c hc0 hcE hc g
    have h1 := span_trace r E htr (span_mul r E hc (hent g j i))
    rw [Matrix.single_mul_single_same, Matrix.trace_single_eq_same] at h1
    have h2 := mul_mem (inv_mem hcE) h1
    rwa [inv_mul_cancel_left₀ hc0] at h2
  have e30 := hQE 0 3 _ hs hsE (hent gs 0 3)
  have e21 := hQE 1 2 _ hgt htE (hent gt 1 2)
  have e03 := hQE 3 0 _ h30 (e30 g30) (hent g30 3 0)
  have e12 := hQE 2 1 _ h21 (e21 g21) (hent g21 2 1)
  have ed : ∀ i g, r g i i ∈ E := fun i => hQE i i 1 one_ne_zero (one_mem E) (he i)
  intro g i j
  by_cases hij : i = j
  · subst hij
    exact ed i g
  by_cases hy : wt i j ∈ yY
  · rcases wt_off i j hij hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact e12 g
    · exact e21 g
    · exact e03 g
    · exact e30 g
  · rw [hS g i j hij hy]
    exact zero_mem E

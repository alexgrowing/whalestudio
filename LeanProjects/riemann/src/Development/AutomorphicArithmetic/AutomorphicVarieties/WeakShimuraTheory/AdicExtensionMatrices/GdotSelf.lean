import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

private def gdot (u v : ℤ × ℤ) : ℤ := u.1 * v.1 + u.2 * v.2

private theorem gdot_self (i j : Fin 4) (h : i ≠ j) : 0 < gdot (wt i j) (wt i j) := by
  revert i j; decide

private theorem gdot_neg (i j k l : Fin 4) (h : gdot (wt i j) (wt k l) < 0) :
    j = k ∨ l = i ∨ j = l.rev ∨ k.rev = i := by
  revert i j k l; decide

private theorem wt_add' (i j k : Fin 4) : wt i k = wt i j + wt j k := by
  simp [wt]

private theorem sgn_sq (i j : Fin 4) : (sgn i * sgn j) * (sgn i * sgn j) = 1 := by
  revert i j; decide

private theorem gdot_sum {α : Type} (f : α → ℤ × ℤ) (u : ℤ × ℤ) (L : List α) (h : ∀ b ∈ L, 0 ≤ gdot u (f b)) :
    0 ≤ gdot u (L.map f).sum := by
  induction L with
  | nil => simp [gdot]
  | cons b L ih =>
    have hb := h b List.mem_cons_self
    have hL := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have e : gdot u ((b :: L).map f).sum = gdot u (f b) + gdot u (L.map f).sum := by
      simp only [List.map_cons, List.sum_cons, gdot, Prod.fst_add, Prod.snd_add]
      ring
    rw [e]
    exact add_nonneg hb hL

variable {A : Type} [CommRing A] {𝓡 : Subring (M4 A)}

private theorem gflip (ha : ∀ x ∈ 𝓡, adj x ∈ 𝓡) {x : M4 A} (hx : x ∈ 𝓡) (i j : Fin 4) :
    ∃ x' ∈ 𝓡, x' j.rev i.rev = x i j := by
  refine ⟨(sgn j.rev * sgn i.rev) • adj x, zsmul_mem (ha x hx) _, ?_⟩
  rw [Matrix.smul_apply, adj_apply, Fin.rev_rev, Fin.rev_rev, smul_smul, sgn_sq, one_smul]

private theorem gcomp (h1 : ∀ i, Matrix.single i i 1 ∈ 𝓡) {x y : M4 A} (hx : x ∈ 𝓡) (hy : y ∈ 𝓡) (i j k : Fin 4) :
    ∃ z ∈ 𝓡, z i k = x i j * y j k := by
  refine ⟨x * Matrix.single j j 1 * y, mul_mem (mul_mem hx (h1 j)) hy, ?_⟩
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

private theorem gmerge (h1 : ∀ i, Matrix.single i i 1 ∈ 𝓡) (ha : ∀ x ∈ 𝓡, adj x ∈ 𝓡) {x y : M4 A} (hx : x ∈ 𝓡)
    (hy : y ∈ 𝓡) (i j k l : Fin 4) (h : gdot (wt i j) (wt k l) < 0) :
    ∃ z ∈ 𝓡, ∃ p q, wt p q = wt i j + wt k l ∧ z p q = x i j * y k l := by
  obtain hjk | hli | hjl | hki := gdot_neg i j k l h
  · subst hjk
    obtain ⟨z, hz, hz'⟩ := gcomp h1 hx hy i j l
    exact ⟨z, hz, i, l, wt_add' i j l, hz'⟩
  · subst hli
    obtain ⟨z, hz, hz'⟩ := gcomp h1 hy hx k l j
    exact ⟨z, hz, k, j, by rw [wt_add' k l j, add_comm], by rw [hz', mul_comm]⟩
  · subst hjl
    obtain ⟨y', hy', hy''⟩ := gflip ha hy k l
    obtain ⟨z, hz, hz'⟩ := gcomp h1 hx hy' i l.rev k.rev
    exact ⟨z, hz, i, k.rev, by rw [wt_add' i l.rev k.rev, wt_rev], by rw [hz', hy'']⟩
  · subst hki
    obtain ⟨x', hx', hx''⟩ := gflip ha hx k.rev j
    rw [Fin.rev_rev] at hx''
    obtain ⟨z, hz, hz'⟩ := gcomp h1 hx' hy j.rev k l
    exact ⟨z, hz, j.rev, l, by rw [wt_add' j.rev k l, ← wt_rev k.rev j, Fin.rev_rev], by rw [hz', hx'']⟩

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxGma :
    ∀ {A : Type} [CommRing A] (E : Subring A) (𝓡 : Subring (M4 A)), (∀ i, Matrix.single i i 1 ∈ 𝓡) → (∀ x ∈ 𝓡, x.trace ∈ E) → (∀ x ∈ 𝓡, adj x ∈ 𝓡) → ∀ L : List (M4 A × Fin 4 × Fin 4), (∀ x ∈ L, x.1 ∈ 𝓡) → (L.map fun x => wt x.2.1 x.2.2).sum = 0 → (L.map fun x => x.1 x.2.1 x.2.2).prod ∈ E := by
  intro A _ E 𝓡 h1 htr ha L hL hsum
  have hdiag : ∀ x ∈ 𝓡, ∀ p, x p p ∈ E := by
    intro x hx p
    have h := htr _ (mul_mem (h1 p) hx)
    have e : (Matrix.single p p 1 * x : M4 A).trace = x p p := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
    rwa [e] at h
  suffices key : ∀ n (L : List (M4 A × Fin 4 × Fin 4)), L.length = n → (∀ x ∈ L, x.1 ∈ 𝓡) →
      (L.map fun x => wt x.2.1 x.2.2).sum = 0 → (L.map fun x => x.1 x.2.1 x.2.2).prod ∈ E from
    key _ L rfl hL hsum
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn hL hsum
  cases L with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    exact E.one_mem
  | cons a rest =>
    obtain ⟨x, i, j⟩ := a
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hsum ⊢
    have hx : x ∈ 𝓡 := hL _ List.mem_cons_self
    have hrest : ∀ y ∈ rest, y.1 ∈ 𝓡 := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    have hlen : rest.length < n := by
      simp at hn
      omega
    by_cases hij : i = j
    · subst hij
      have hs : (rest.map fun x => wt x.2.1 x.2.2).sum = 0 := by
        rw [(wt_eq_zero i i).2 rfl, zero_add] at hsum
        exact hsum
      exact mul_mem (hdiag x hx i) (ih _ hlen rest rfl hrest hs)
    · have hpos := UpperTheory.V.Ws.gdot_self i j hij
      have hneg : ∃ b ∈ rest, UpperTheory.V.Ws.gdot (wt i j) (wt b.2.1 b.2.2) < 0 := by
        by_contra hcon
        push_neg at hcon
        have h0 := UpperTheory.V.Ws.gdot_sum (fun b : M4 A × Fin 4 × Fin 4 => wt b.2.1 b.2.2) (wt i j) rest hcon
        have e : UpperTheory.V.Ws.gdot (wt i j) (wt i j + (rest.map fun b => wt b.2.1 b.2.2).sum) =
            UpperTheory.V.Ws.gdot (wt i j) (wt i j) + UpperTheory.V.Ws.gdot (wt i j) (rest.map fun b => wt b.2.1 b.2.2).sum := by
          simp only [UpperTheory.V.Ws.gdot, Prod.fst_add, Prod.snd_add]
          ring
        have e0 : UpperTheory.V.Ws.gdot (wt i j) 0 = 0 := by simp [UpperTheory.V.Ws.gdot]
        rw [hsum, e0] at e
        linarith
      obtain ⟨b, hb, hbneg⟩ := hneg
      obtain ⟨y, k, l⟩ := b
      have hy : y ∈ 𝓡 := hrest _ hb
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
      obtain ⟨z, hz, p, q, hw, hzv⟩ := UpperTheory.V.Ws.gmerge h1 ha hx hy i j k l hbneg
      have hlen' : ((z, p, q) :: (s ++ t)).length < n := by
        simp at hn ⊢
        omega
      have hL' : ∀ w ∈ ((z, p, q) :: (s ++ t)), w.1 ∈ 𝓡 := by
        intro w hw'
        simp only [List.mem_cons, List.mem_append] at hw'
        rcases hw' with rfl | hw' | hw'
        · exact hz
        · exact hrest w (by simp [hw'])
        · exact hrest w (by simp [hw'])
      have hsum' : (((z, p, q) :: (s ++ t)).map fun x => wt x.2.1 x.2.2).sum = 0 := by
        simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append] at hsum ⊢
        rw [hw]
        linear_combination hsum
      have := ih _ hlen' _ rfl hL' hsum'
      simp only [List.map_cons, List.map_append, List.prod_cons, List.prod_append] at this ⊢
      rw [hzv] at this
      convert this using 1
      ring

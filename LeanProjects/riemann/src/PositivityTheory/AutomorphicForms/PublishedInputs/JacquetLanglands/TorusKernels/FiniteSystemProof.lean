import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open scoped NNReal

namespace UpperTheory.Esk.Fin0Aux

theorem nat_le_one (ν : Valuation ℂ ℝ≥0) (n : ℕ) : ν (n : ℂ) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le ν ih (by simp)

theorem step (ν : Valuation ℂ ℝ≥0) (l : ℕ) (hl : l.Prime) (y : ℂ) (hy : ν y ≤ 1) :
    ν ((1 + y) ^ l - 1) ≤ max (ν (l : ℂ)) (ν y) * ν y := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by have := hl.two_le; omega⟩
  have e : (1 + y) ^ (m + 2) - 1 =
      ∑ k ∈ Finset.range (m + 1), y ^ (k + 1) * ((m + 2).choose (k + 1) : ℂ) + y ^ (m + 2) := by
    rw [add_comm (1 : ℂ) y, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one]
    ring
  rw [e]
  apply Valuation.map_add_le
  · apply Valuation.map_sum_le
    intro k hk
    have hk' := Finset.mem_range.1 hk
    obtain ⟨q, hq⟩ := hl.dvd_choose_self (Nat.succ_ne_zero k) (by omega)
    rw [Valuation.map_mul, hq, Nat.cast_mul, Valuation.map_mul, Valuation.map_pow]
    have h1 : ν y ^ (k + 1) ≤ ν y := by
      rw [pow_succ]; exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hy)
    have h2 := nat_le_one ν q
    calc ν y ^ (k + 1) * (ν ((m + 2 : ℕ) : ℂ) * ν (q : ℂ)) ≤ ν y * (ν ((m + 2 : ℕ) : ℂ) * 1) := by gcongr
      _ ≤ max (ν ((m + 2 : ℕ) : ℂ)) (ν y) * ν y := by
          rw [mul_one, mul_comm]; gcongr; exact le_max_left _ _
  · rw [Valuation.map_pow]
    calc ν y ^ (m + 2) ≤ ν y ^ 2 := pow_le_pow_of_le_one zero_le hy (by omega)
      _ = ν y * ν y := sq _
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem iter (ν : Valuation ℂ ℝ≥0) (l : ℕ) (hl : l.Prime) (hνl : ν (l : ℂ) < 1) (x : ℂ) (hx : ν x < 1) :
    ∀ a : ℕ, ν ((1 + x) ^ (l ^ a) - 1) ≤ max (ν (l : ℂ)) (ν x) ^ a * ν x := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have e : (1 + x) ^ (l ^ (a + 1)) - 1 = (1 + ((1 + x) ^ (l ^ a) - 1)) ^ l - 1 := by
      rw [add_sub_cancel, ← pow_mul, ← pow_succ]
    rw [e]
    have hθ : max (ν (l : ℂ)) (ν x) ≤ 1 := max_le hνl.le hx.le
    have hya : ν ((1 + x) ^ (l ^ a) - 1) ≤ ν x :=
      ih.trans (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hθ))
    calc _ ≤ max (ν (l : ℂ)) (ν ((1 + x) ^ (l ^ a) - 1)) * ν ((1 + x) ^ (l ^ a) - 1) :=
          step ν l hl _ (hya.trans hx.le)
      _ ≤ max (ν (l : ℂ)) (ν x) * (max (ν (l : ℂ)) (ν x) ^ a * ν x) :=
          mul_le_mul (max_le_max le_rfl hya) ih zero_le zero_le
      _ = max (ν (l : ℂ)) (ν x) ^ (a + 1) * ν x := by ring

def lam {J : Type} (S : Finset (J → ℂ)) (a : (J → ℂ) → ℂ) : ((J → ℂ) → ℂ) →ₗ[ℂ] ℂ :=
  ∑ s ∈ S, a s • (LinearMap.proj s : ((J → ℂ) → ℂ) →ₗ[ℂ] ℂ)

theorem lam_apply {J : Type} (S : Finset (J → ℂ)) (a : (J → ℂ) → ℂ) (g : (J → ℂ) → ℂ) :
    lam S a g = ∑ s ∈ S, a s * g s := by
  simp [lam, LinearMap.sum_apply]

theorem factors {J : Type} (ν : Valuation ℂ ℝ≥0) (Λ : ((J → ℂ) → ℂ) →ₗ[ℂ] ℂ) (P : List J → Prop)
    (hP : ∀ W j, P W → P (W ++ [j])) (B : ℝ≥0) (hB : ∀ W, P W → ν (Λ fun s => (W.map s).prod) ≤ B) :
    ∀ (Fs : List (ℂ × J × ℂ)), (∀ f ∈ Fs, ν f.1 ≤ 1 ∧ ν f.2.2 ≤ 1) → ∀ W, P W →
      ν (Λ fun s => (W.map s).prod * (Fs.map fun f => f.1 * s f.2.1 + f.2.2).prod) ≤ B := by
  intro Fs
  induction Fs with
  | nil => intro _ W hW; simpa using hB W hW
  | cons f Fs ih =>
    intro hF W hW
    have hf := hF f List.mem_cons_self
    have hF' : ∀ g ∈ Fs, ν g.1 ≤ 1 ∧ ν g.2.2 ≤ 1 := fun g hg => hF g (List.mem_cons_of_mem _ hg)
    have e : (fun s : J → ℂ => (W.map s).prod * ((f :: Fs).map fun f => f.1 * s f.2.1 + f.2.2).prod) =
        f.1 • (fun s : J → ℂ => ((W ++ [f.2.1]).map s).prod * (Fs.map fun f => f.1 * s f.2.1 + f.2.2).prod) +
        f.2.2 • (fun s : J → ℂ => (W.map s).prod * (Fs.map fun f => f.1 * s f.2.1 + f.2.2).prod) := by
      funext s
      simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append, List.map_nil,
        List.prod_nil, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    apply Valuation.map_add_le
    · rw [Valuation.map_mul]
      calc _ ≤ 1 * B := mul_le_mul' hf.1 (ih hF' _ (hP W _ hW))
        _ = B := one_mul B
    · rw [Valuation.map_mul]
      calc _ ≤ 1 * B := mul_le_mul' hf.2 (ih hF' _ hW)
        _ = B := one_mul B

theorem count_rep {J : Type} [DecidableEq J] (l : List J) (j : J) (n : ℕ) :
    ((List.replicate n l).flatten).count j = n * l.count j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.count_append, ih]; ring

theorem prod_rep {α : Type} (l : List α) (g : α → ℂ) (n : ℕ) :
    (((List.replicate n l).flatten).map g).prod = (l.map g).prod ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append, ih, pow_succ']

theorem prod_near_one (ν : Valuation ℂ ℝ≥0) (l : List ℂ) (h : ∀ y ∈ l, ν (y - 1) < 1) : ν (l.prod - 1) < 1 := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have hy := h y List.mem_cons_self
    have hl := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    have hP : ν l.prod ≤ 1 := by
      have : l.prod = (l.prod - 1) + 1 := by ring
      rw [this]; exact Valuation.map_add_le ν hl.le (by simp)
    rw [List.prod_cons, show y * l.prod - 1 = (y - 1) * l.prod + (l.prod - 1) by ring]
    apply Valuation.map_add_lt ν _ hl
    rw [Valuation.map_mul]
    calc ν (y - 1) * ν l.prod ≤ ν (y - 1) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hy

theorem integral {J : Type} [DecidableEq J] (ν : Valuation ℂ ℝ≥0) (L : Finset J) (S : Finset (J → ℂ))
    (a : (J → ℂ) → ℂ)
    (hB : ∀ W : List J, (∀ j ∈ L, 1 ≤ W.count j) → ν (∑ s ∈ S, a s * (W.map s).prod) ≤ 1)
    (t : J → ℂ) (ht : t ∈ S) (hat : a t ≠ 0) (htL : ∀ j ∈ L, t j ≠ 0) (j0 : J) : ν (t j0) ≤ 1 := by
  classical
  have hj : ∀ u ∈ S.erase t, ∃ j, u j ≠ t j := by
    intro u hu
    by_contra h
    push_neg at h
    exact (Finset.ne_of_mem_erase hu) (funext h)
  have : Nonempty J := ⟨j0⟩
  choose! jj hjj using hj
  let c : ℂ → ℂ := fun x => if ν x ≤ 1 then 1 else x⁻¹
  have hc : ∀ x, ν (c x) ≤ 1 ∧ ν (c x * x) ≤ 1 ∧ c x ≠ 0 := by
    intro x
    by_cases hx : ν x ≤ 1
    · simp only [c, if_pos hx, one_mul]; exact ⟨by simp, hx, one_ne_zero⟩
    · simp only [c, if_neg hx]
      push_neg at hx
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx
      refine ⟨?_, ?_, inv_ne_zero hx0⟩
      · rw [map_inv₀]; exact inv_le_one_of_one_le₀ hx.le
      · rw [inv_mul_cancel₀ hx0]; simp
  let Fs : List (ℂ × J × ℂ) :=
    (S.erase t).toList.map fun u => (c (u (jj u)), jj u, -(c (u (jj u)) * u (jj u)))
  have hFs : ∀ f ∈ Fs, ν f.1 ≤ 1 ∧ ν f.2.2 ≤ 1 := by
    intro f hf
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hf
    exact ⟨(hc _).1, by rw [Valuation.map_neg]; exact (hc _).2.1⟩
  have hP : ∀ (W : List J) (j : J), (∀ i ∈ L, 1 ≤ W.count i) → (∀ i ∈ L, 1 ≤ (W ++ [j]).count i) := by
    intro W j hW i hi
    rw [List.count_append]
    have := hW i hi
    omega
  have key := factors ν (lam S a) (fun W => ∀ j ∈ L, 1 ≤ W.count j) hP 1
    (fun W hW => by rw [lam_apply]; exact hB W hW) Fs hFs
  have hR0 : ∀ u ∈ S, u ≠ t → (Fs.map fun f => f.1 * u f.2.1 + f.2.2).prod = 0 := by
    intro u hu hne
    apply List.prod_eq_zero
    refine List.mem_map.2 ⟨(c (u (jj u)), jj u, -(c (u (jj u)) * u (jj u))), ?_, ?_⟩
    · exact List.mem_map.2 ⟨u, Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hne, hu⟩), rfl⟩
    · simp
  have hRt : (Fs.map fun f => f.1 * t f.2.1 + f.2.2).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro h
    obtain ⟨f, hf, hf0⟩ := List.mem_map.1 h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hf
    have hu' := Finset.mem_toList.1 hu
    have e : c (u (jj u)) * t (jj u) + -(c (u (jj u)) * u (jj u)) = c (u (jj u)) * (t (jj u) - u (jj u)) := by ring
    simp only at hf0
    rw [e] at hf0
    rcases mul_eq_zero.1 hf0 with h1 | h1
    · exact (hc _).2.2 h1
    · exact hjj u hu' (sub_eq_zero.1 h1).symm
  set K := a t * (L.toList.map t).prod * (Fs.map fun f => f.1 * t f.2.1 + f.2.2).prod with hKdef
  have hK : K ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hat ?_) hRt
    apply List.prod_ne_zero
    intro h
    obtain ⟨j, hj, hj0⟩ := List.mem_map.1 h
    exact htL j (Finset.mem_toList.1 hj) hj0
  have hn : ∀ n : ℕ, ν K * ν (t j0) ^ n ≤ 1 := by
    intro n
    have := key (L.toList ++ List.replicate n j0) (by
      intro j hj
      rw [List.count_append]
      have : 1 ≤ L.toList.count j := List.count_pos_iff.2 (Finset.mem_toList.2 hj)
      omega)
    rw [lam_apply, Finset.sum_eq_single t (fun u hu hne => mul_eq_zero_of_right _
      (mul_eq_zero_of_right _ (hR0 u hu hne))) (fun h => absurd ht h)] at this
    have e : a t * (((L.toList ++ List.replicate n j0).map t).prod *
        (Fs.map fun f => f.1 * t f.2.1 + f.2.2).prod) = K * t j0 ^ n := by
      rw [hKdef, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]; ring
    rwa [e, Valuation.map_mul, Valuation.map_pow] at this
  by_contra hlt
  push_neg at hlt
  have hK0 : 0 < ν K := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff ν).2 hK)
  obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt (ν K)⁻¹ hlt
  have h1 : ν K * (ν K)⁻¹ < ν K * ν (t j0) ^ n := mul_lt_mul_of_pos_left hn' hK0
  rw [mul_inv_cancel₀ hK0.ne'] at h1
  exact absurd (hn n) (not_le.2 h1)

end UpperTheory.Esk.Fin0Aux

open UpperTheory.Esk.Fin0Aux in
theorem UpperTheory.Esk.finite_system_proof : UpperTheory.Esk.Sys → UpperTheory.Esk.Fin0 := by
  intro hSys ν l hl hνl J V V' _ _ _ _ _ _ _ T T' hT hT' L ε ρ hρ hε hW f s hf0 hfs hsL
  classical
  obtain ⟨S, m, hS, hm, hmsum, htr⟩ := hSys J V T hT
  obtain ⟨S', m', hS', hm', -, htr'⟩ := hSys J V' T' hT'

  have intV : ∀ u ∈ S, (∀ j ∈ L, u j ≠ 0) → ∀ j, ν (u j) ≤ 1 := fun u hu huL j =>
    integral ν L S (fun s => (m s : ℂ)) (fun W hW' => by rw [← htr W]; exact (hW W 1 le_rfl hW').1) u hu
      (Nat.cast_ne_zero.2 (by have := hm u hu; omega)) huL j
  have intV' : ∀ u ∈ S', (∀ j ∈ L, u j ≠ 0) → ∀ j, ν (u j) ≤ 1 := fun u hu huL j =>
    integral ν L S' (fun s => (m' s : ℂ)) (fun W hW' => by rw [← htr' W]; exact (hW W 1 le_rfl hW').2.1) u hu
      (Nat.cast_ne_zero.2 (by have := hm' u hu; omega)) huL j
  have hsS : s ∈ S := (hS s).2 ⟨f, hf0, hfs⟩
  have hs0 : ∀ j ∈ L, s j ≠ 0 := fun j hj h => by have := hsL j hj; rw [h, map_zero] at this; exact zero_ne_one this
  have hsint : ∀ j, ν (s j) ≤ 1 := intV s hsS hs0
  by_contra hcon
  push_neg at hcon
  have hS'nc : ∀ u ∈ S', ∃ j, 1 ≤ ν (u j - s j) := by
    intro u hu
    obtain ⟨f', hf', hu'⟩ := (hS' u).1 hu
    exact hcon f' u hf' hu'
  rcases isEmpty_or_nonempty J with hJ | hJ
  · have hS'e : S' = ∅ := Finset.eq_empty_of_forall_notMem fun u hu => by
      obtain ⟨j, -⟩ := hS'nc u hu; exact (IsEmpty.false j).elim
    have hd1 : 1 ≤ Module.finrank ℂ V :=
      hmsum ▸ (hm s hsS).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hsS)
    have hεd := hε _ hd1 le_rfl
    obtain ⟨r, hr⟩ := NNReal.exists_pow_lt_of_lt_one (lt_of_le_of_lt zero_le hεd) hρ
    have := (hW [] (r + 1) (by omega) (fun j _ => (IsEmpty.false j).elim)).2.2
    rw [htr, htr', hS'e, Finset.sum_empty, sub_zero] at this
    simp only [List.map_nil, List.prod_nil, mul_one] at this
    rw [← Nat.cast_sum, hmsum] at this
    exact absurd this (not_le.2 (max_lt hεd ((pow_le_pow_of_le_one zero_le hρ.le (by omega)).trans_lt hr)))

  let NC : Finset (J → ℂ) := (S ∪ S').filter fun u => (∀ j ∈ L, u j ≠ 0) ∧ ∃ j, 1 ≤ ν (u j - s j)
  have hNC : ∀ u ∈ NC, ∃ j, 1 ≤ ν (u j - s j) := fun u hu => (Finset.mem_filter.1 hu).2.2
  choose! jn hjn using hNC
  have hNCint : ∀ u ∈ NC, ∀ j, ν (u j) ≤ 1 := by
    intro u hu j
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hu
    rcases Finset.mem_union.1 h1 with h | h
    · exact intV u h h2 j
    · exact intV' u h h2 j
  have hne : ∀ u ∈ NC, s (jn u) - u (jn u) ≠ 0 := by
    intro u hu h
    have := hjn u hu
    rw [Valuation.map_sub_swap, h, map_zero] at this
    exact absurd this (by simp)
  let Fl : List (ℂ × J × ℂ) := NC.toList.map fun v =>
    ((s (jn v) - v (jn v))⁻¹, jn v, -(v (jn v) * (s (jn v) - v (jn v))⁻¹))
  have hFl : ∀ f ∈ Fl, ν f.1 ≤ 1 ∧ ν f.2.2 ≤ 1 := by
    intro f hf
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hf
    have hv' := Finset.mem_toList.1 hv
    have h1 : ν (s (jn v) - v (jn v))⁻¹ ≤ 1 := by
      rw [map_inv₀, Valuation.map_sub_swap]; exact inv_le_one_of_one_le₀ (hjn v hv')
    refine ⟨h1, ?_⟩
    rw [Valuation.map_neg, Valuation.map_mul]
    calc ν (v (jn v)) * ν (s (jn v) - v (jn v))⁻¹ ≤ 1 * 1 := mul_le_mul' (hNCint v hv' _) h1
      _ = 1 := one_mul 1
  let G : (J → ℂ) → ℂ := fun u => (L.toList.map u).prod * (Fl.map fun f => f.1 * u f.2.1 + f.2.2).prod
  have hG0 : ∀ u ∈ S ∪ S', (∃ j, 1 ≤ ν (u j - s j)) → G u = 0 := by
    intro u hu hnc
    by_cases hI : ∀ j ∈ L, u j ≠ 0
    · have huNC : u ∈ NC := Finset.mem_filter.2 ⟨hu, hI, hnc⟩
      apply mul_eq_zero_of_right
      apply List.prod_eq_zero
      refine List.mem_map.2 ⟨((s (jn u) - u (jn u))⁻¹, jn u, -(u (jn u) * (s (jn u) - u (jn u))⁻¹)), ?_, ?_⟩
      · exact List.mem_map.2 ⟨u, Finset.mem_toList.2 huNC, rfl⟩
      · simp only; ring
    · push_neg at hI
      obtain ⟨j, hj, hj0⟩ := hI
      apply mul_eq_zero_of_left
      apply List.prod_eq_zero
      exact List.mem_map.2 ⟨j, Finset.mem_toList.2 hj, hj0⟩
  let Cinv : ℂ := (L.toList.map fun j => (s j)⁻¹).prod
  have hCinv : ν Cinv = 1 := by
    have : ∀ l' : List J, (∀ j ∈ l', j ∈ L) → ν (l'.map fun j => (s j)⁻¹).prod = 1 := by
      intro l' hl'
      induction l' with
      | nil => simp
      | cons j l' ih =>
        rw [List.map_cons, List.prod_cons, Valuation.map_mul, map_inv₀, hsL j (hl' j List.mem_cons_self),
          ih fun i hi => hl' i (List.mem_cons_of_mem _ hi)]
        simp
    exact this _ fun j hj => Finset.mem_toList.1 hj

  let cong : Finset (J → ℂ) := S.filter fun u => ∀ j, ν (u j - s j) < 1
  have hcong : ∀ u ∈ cong, ν (Cinv * G u - 1) < 1 := by
    intro u hu
    have hu' := (Finset.mem_filter.1 hu).2
    have e : Cinv * G u = ((L.toList.map fun j => u j * (s j)⁻¹) ++
        (Fl.map fun f => f.1 * u f.2.1 + f.2.2)).prod := by
      rw [List.prod_append, List.prod_map_mul]
      simp only [G, Cinv]; ring
    rw [e]
    apply prod_near_one
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      have hsj := hs0 j (Finset.mem_toList.1 hj)
      rw [show u j * (s j)⁻¹ - 1 = (u j - s j) * (s j)⁻¹ by field_simp, Valuation.map_mul, map_inv₀,
        hsL j (Finset.mem_toList.1 hj), inv_one, mul_one]
      exact hu' j
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hf
      have hv' := Finset.mem_toList.1 hv
      have hn0 := hne v hv'
      simp only
      rw [show (s (jn v) - v (jn v))⁻¹ * u (jn v) + -(v (jn v) * (s (jn v) - v (jn v))⁻¹) - 1 =
          (u (jn v) - s (jn v)) * (s (jn v) - v (jn v))⁻¹ by field_simp; ring]
      rw [Valuation.map_mul]
      have h1 : ν (s (jn v) - v (jn v))⁻¹ ≤ 1 := by
        rw [map_inv₀, Valuation.map_sub_swap]; exact inv_le_one_of_one_le₀ (hjn v hv')
      calc ν (u (jn v) - s (jn v)) * ν (s (jn v) - v (jn v))⁻¹ ≤ ν (u (jn v) - s (jn v)) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hu' _
  set d : ℕ := ∑ u ∈ cong, m u with hd
  have hscong : s ∈ cong := Finset.mem_filter.2 ⟨hsS, fun j => by simp⟩
  have hd1 : 1 ≤ d := (hm s hsS).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hscong)
  have hd2 : d ≤ Module.finrank ℂ V := hmsum ▸ Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hεd := hε d hd1 hd2
  have hd0 : 0 < ν (d : ℂ) := lt_of_le_of_lt zero_le hεd

  let τ : ℝ≥0 := cong.sup fun u => ν (Cinv * G u - 1)
  have hτ : τ < 1 := by
    rw [Finset.sup_lt_iff zero_lt_one]
    exact hcong
  set θ : ℝ≥0 := max (max (ν (l : ℂ)) τ) ρ with hθdef
  have hθ : θ < 1 := max_lt (max_lt hνl hτ) hρ
  obtain ⟨a, ha⟩ := NNReal.exists_pow_lt_of_lt_one hd0 hθ
  set n : ℕ := l ^ a with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hl.ne_zero)

  have hbound : ν ((lam S (fun u => (m u : ℂ)) - lam S' (fun u => (m' u : ℂ))) fun u => G u ^ n) ≤ max ε (ρ ^ n) := by
    have key := factors ν (lam S (fun u => (m u : ℂ)) - lam S' (fun u => (m' u : ℂ)))
      (fun W => ∀ j ∈ L, n ≤ W.count j)
      (fun W j hW i hi => by rw [List.count_append]; have := hW i hi; omega) (max ε (ρ ^ n))
      (fun W hW' => by
        rw [LinearMap.sub_apply, lam_apply, lam_apply, ← htr W, ← htr' W]
        exact (hW W n hn1 hW').2.2)
      ((List.replicate n Fl).flatten) (by
        intro f hf
        obtain ⟨l', hl', hfl⟩ := List.mem_flatten.1 hf
        rw [List.eq_of_mem_replicate hl'] at hfl
        exact hFl f hfl)
      ((List.replicate n L.toList).flatten) (by
        intro j hj
        rw [count_rep]
        have : 1 ≤ L.toList.count j := List.count_pos_iff.2 (Finset.mem_toList.2 hj)
        nlinarith)
    convert key using 3
    funext u
    rw [prod_rep, prod_rep, mul_pow]

  have hval : Cinv ^ n * ((lam S (fun u => (m u : ℂ)) - lam S' (fun u => (m' u : ℂ))) fun u => G u ^ n) =
      (d : ℂ) + ∑ u ∈ cong, (m u : ℂ) * ((1 + (Cinv * G u - 1)) ^ n - 1) := by
    rw [LinearMap.sub_apply, lam_apply, lam_apply, mul_sub, Finset.mul_sum, Finset.mul_sum]
    have h2 : ∑ u ∈ S', Cinv ^ n * ((m' u : ℂ) * G u ^ n) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [hG0 u (Finset.mem_union_right _ hu) (hS'nc u hu), zero_pow (by omega)]
      ring
    have h1 : ∑ u ∈ S, Cinv ^ n * ((m u : ℂ) * G u ^ n) = ∑ u ∈ cong, (m u : ℂ) * (Cinv * G u) ^ n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      split_ifs with hc
      · ring
      · push_neg at hc
        rw [hG0 u (Finset.mem_union_left _ hu) (by obtain ⟨j, hj⟩ := hc; exact ⟨j, hj⟩), zero_pow (by omega)]
        ring
    rw [h1, h2, sub_zero, hd]
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hsmall : ν (∑ u ∈ cong, (m u : ℂ) * ((1 + (Cinv * G u - 1)) ^ n - 1)) ≤ θ ^ a := by
    apply Valuation.map_sum_le
    intro u hu
    rw [Valuation.map_mul]
    have hx := hcong u hu
    have h1 := iter ν l hl hνl _ hx a
    have hle : ν (Cinv * G u - 1) ≤ τ := Finset.le_sup (f := fun u => ν (Cinv * G u - 1)) hu
    calc ν (m u : ℂ) * ν ((1 + (Cinv * G u - 1)) ^ n - 1)
        ≤ 1 * (max (ν (l : ℂ)) (ν (Cinv * G u - 1)) ^ a * 1) :=
          mul_le_mul' (nat_le_one ν _) (h1.trans (mul_le_mul' le_rfl hx.le))
      _ ≤ θ ^ a := by
          rw [one_mul, mul_one]
          exact pow_le_pow_left₀ zero_le ((max_le_max le_rfl hle).trans (le_max_left _ _)) a
  have hρn : ρ ^ n ≤ θ ^ a :=
    (pow_le_pow_of_le_one zero_le hρ.le (Nat.lt_pow_self hl.one_lt).le).trans
      (pow_le_pow_left₀ zero_le (le_max_right _ _) a)
  have hdeq : (d : ℂ) = Cinv ^ n * ((lam S (fun u => (m u : ℂ)) - lam S' (fun u => (m' u : ℂ))) fun u => G u ^ n) -
      ∑ u ∈ cong, (m u : ℂ) * ((1 + (Cinv * G u - 1)) ^ n - 1) := by
    rw [hval]; ring
  have hfin : ν (d : ℂ) ≤ max (max ε (ρ ^ n)) (θ ^ a) := by
    rw [hdeq]
    apply Valuation.map_sub_le
    · rw [Valuation.map_mul, Valuation.map_pow, hCinv, one_pow, one_mul]
      exact hbound.trans (le_max_left _ _)
    · exact hsmall.trans (le_max_right _ _)
  have : max (max ε (ρ ^ n)) (θ ^ a) < ν (d : ℂ) := max_lt (max_lt hεd (hρn.trans_lt ha)) ha
  exact absurd hfin (not_le.2 this)

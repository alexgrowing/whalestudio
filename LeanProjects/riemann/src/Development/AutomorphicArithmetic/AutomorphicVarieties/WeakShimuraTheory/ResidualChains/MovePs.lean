import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def UpperTheory.V.Ws.Chain.uu {k : Type} [CommRing k] (y : k) : M4 k := !![1, 0, 0, 0; 0, 1, 0, 0; y, 0, 1, 0; 0, y, 0, 1]

private theorem adj_mul_M4 {k : Type} [Field k] (A B : M4 k) : adj (A * B) = adj B * adj A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj, sgn, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem adj_uu_mul_diag_mul_uu_eq_of_diag_pairs {k : Type} [Field k] (z : k) (D : M4 k) (hD : ∀ i j : Fin 4, i ≠ j → D i j = 0)
    (h02 : D 0 0 = D 2 2) (h13 : D 1 1 = D 3 3) :
    adj (UpperTheory.V.Ws.Chain.uu z) * D * UpperTheory.V.Ws.Chain.uu z = D := by
  have e01 := hD 0 1 (by decide)
  have e02 := hD 0 2 (by decide)
  have e03 := hD 0 3 (by decide)
  have e10 := hD 1 0 (by decide)
  have e12 := hD 1 2 (by decide)
  have e13 := hD 1 3 (by decide)
  have e20 := hD 2 0 (by decide)
  have e21 := hD 2 1 (by decide)
  have e23 := hD 2 3 (by decide)
  have e30 := hD 3 0 (by decide)
  have e31 := hD 3 1 (by decide)
  have e32 := hD 3 2 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj, sgn, UpperTheory.V.Ws.Chain.uu, Matrix.mul_apply, Fin.sum_univ_four,
      e01, e02, e03, e10, e12, e13, e20, e21, e23, e30, e31, e32]
  all_goals (simp only [h02, h13]; ring)

private theorem adj_uu_mul_uu_eq_one {k : Type} [Field k] (z : k) :
    adj (UpperTheory.V.Ws.Chain.uu z) * UpperTheory.V.Ws.Chain.uu z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj, sgn, UpperTheory.V.Ws.Chain.uu, Matrix.mul_apply, Fin.sum_univ_four]

private theorem mul_lowerTriangular_M4 {k : Type} [Field k] (A B : M4 k) (hA : ∀ i j : Fin 4, i < j → A i j = 0)
    (hB : ∀ i j : Fin 4, i < j → B i j = 0) : ∀ i j : Fin 4, i < j → (A * B) i j = 0 := by
  intro i j h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  rcases lt_or_ge i l with h1 | h1
  · rw [hA i l h1, zero_mul]
  · rw [hB l j (lt_of_le_of_lt h1 h), mul_zero]

private theorem adj_lowerTriangular_M4 {k : Type} [Field k] (A : M4 k) (hA : ∀ i j : Fin 4, i < j → A i j = 0) :
    ∀ i j : Fin 4, i < j → adj A i j = 0 := by
  intro i j h
  simp only [adj, Matrix.of_apply]
  rw [hA j.rev i.rev (Fin.rev_lt_rev.2 h), smul_zero]

private theorem lowerTriangular_of_suppM_neg_wAl {k : Type} [Field k] (X : M4 k) (hX : SuppM {-wAl} X) :
    ∀ i j : Fin 4, i < j → X i j = 0 := by
  intro i j h
  apply hX i j (ne_of_lt h)
  revert h
  fin_cases i <;> fin_cases j <;> decide

private theorem mul_uu_eq_explicit_of_suppM_neg_wAl_unit_diag {k : Type} [Field k] (X : M4 k) (z : k) (hX : SuppM {-wAl} X)
    (hd : ∀ i, X i i = 1) :
    X * UpperTheory.V.Ws.Chain.uu z = !![1, 0, 0, 0; X 1 0, 1, 0, 0; z, 0, 1, 0; X 3 2 * z, z, X 3 2, 1] := by
  have hL := lowerTriangular_of_suppM_neg_wAl X hX
  have e01 := hL 0 1 (by decide)
  have e02 := hL 0 2 (by decide)
  have e03 := hL 0 3 (by decide)
  have e12 := hL 1 2 (by decide)
  have e13 := hL 1 3 (by decide)
  have e23 := hL 2 3 (by decide)
  have e20 := hX 2 0 (by decide) (by decide)
  have e21 := hX 2 1 (by decide) (by decide)
  have e30 := hX 3 0 (by decide) (by decide)
  have e31 := hX 3 1 (by decide) (by decide)
  have d0 := hd 0
  have d1 := hd 1
  have d2 := hd 2
  have d3 := hd 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.V.Ws.Chain.uu, Matrix.mul_apply, Fin.sum_univ_four,
      e01, e02, e03, e12, e13, e23, e20, e21, e30, e31, d0, d1, d2, d3]

theorem UpperTheory.V.Ws.Chain.movePs :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k),
      (∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) → (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) → (∀ v, ∀ s ∈ Φ.Gv v, a (Φ.rt wPs s) = 1) →
      ∀ c : PD Φ.ι Γ k, Φ.IsRes a c → Supp {-wAl} c.r → (∀ v, SuppM {-wAl} (c.n v)) → ∀ y : Φ.ι → k,
      ∃ c' : PD Φ.ι Γ k, Φ.IsRes a c' ∧ c'.r = c.r ∧ ∀ v, SuppM qQ (c'.n v) ∧ c'.n v 1 0 = c.n v 1 0 ∧ c'.n v 2 0 = y v := by
  intro O Γ _ _ _ Φ k _ a hrev hMu hrt c hc hr hn y
  have hnL : ∀ v, ∀ i j : Fin 4, i < j → c.n v i j = 0 := fun v => lowerTriangular_of_suppM_neg_wAl _ (hn v)
  have hrL : ∀ g, ∀ i j : Fin 4, i < j → c.r g i j = 0 := fun g => lowerTriangular_of_suppM_neg_wAl _ (hr g)
  have hnd : ∀ v i, c.n v i i = 1 := fun v => (hc.pair.low v).2.1
  have hform : ∀ v, c.n v * UpperTheory.V.Ws.Chain.uu (y v) =
      !![1, 0, 0, 0; c.n v 1 0, 1, 0, 0; y v, 0, 1, 0; c.n v 3 2 * y v, y v, c.n v 3 2, 1] :=
    fun v => mul_uu_eq_explicit_of_suppM_neg_wAl_unit_diag _ _ (hn v) (hnd v)
  have hkey : ∀ v, ∀ s ∈ Φ.Gv v,
      adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) =
        adj (c.n v) * c.r s * c.n v := by
    intro v s hs
    have hM : adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) =
        adj (UpperTheory.V.Ws.Chain.uu (y v)) * (adj (c.n v) * c.r s * c.n v) * UpperTheory.V.Ws.Chain.uu (y v) := by
      rw [adj_mul_M4]
      simp only [mul_assoc]
    rw [hM]
    have hLM := mul_lowerTriangular_M4 _ _ (mul_lowerTriangular_M4 _ _ (adj_lowerTriangular_M4 _ (hnL v)) (hrL s)) (hnL v)
    have hUp := hc.pair.flag v s hs
    have hch : ∀ i, (adj (c.n v) * c.r s * c.n v) i i = a ↑(Φ.χ i s) := fun i => hc.res.char v s hs i
    have h2ne : a ↑(Φ.χ 2 s) ≠ 0 := ((Φ.χ 2 s).isUnit.map a).ne_zero
    have h02 : a ↑(Φ.χ 0 s) = a ↑(Φ.χ 2 s) := by
      have h := hrt v s hs
      simp [Fr.rt, wPs] at h
      exact (mul_inv_eq_one₀ h2ne).1 h
    have h13 : a ↑(Φ.χ 1 s) = a ↑(Φ.χ 3 s) := by
      have e0 := congrArg (fun u : Oˣ => a ↑u) (hrev 0 s)
      have e1 := congrArg (fun u : Oˣ => a ↑u) (hrev 1 s)
      simp only [Units.val_mul, map_mul] at e0 e1
      have r0 : (0 : Fin 4).rev = 3 := rfl
      have r1 : (1 : Fin 4).rev = 2 := rfl
      rw [r0] at e0
      rw [r1] at e1
      rw [h02] at e0
      have e : a ↑(Φ.χ 2 s) * a ↑(Φ.χ 3 s) = a ↑(Φ.χ 2 s) * a ↑(Φ.χ 1 s) := by
        rw [e0, ← e1]
        ring
      exact (mul_left_cancel₀ h2ne e).symm
    apply adj_uu_mul_diag_mul_uu_eq_of_diag_pairs
    · intro i j hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact hLM i j h
      · exact hUp i j h
    · rw [hch, hch, h02]
    · rw [hch, hch, h13]
  refine ⟨PD.mk c.r (fun v => c.n v * UpperTheory.V.Ws.Chain.uu (y v)), ⟨⟨hc.pair.mult, hc.pair.kill, hc.pair.nrm,
    ?_, ?_, ?_⟩, ⟨hc.res.diag, ?_, ?_⟩, hc.cont⟩, rfl, ?_⟩
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · show adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) = (1 : k) • 1
      rw [adj_mul_M4]
      have hg : adj (c.n v) * c.n v = (1 : k) • 1 := (hc.pair.low v).1
      rw [one_smul] at hg ⊢
      rw [show adj (UpperTheory.V.Ws.Chain.uu (y v)) * adj (c.n v) * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) =
          adj (UpperTheory.V.Ws.Chain.uu (y v)) * (adj (c.n v) * c.n v) * UpperTheory.V.Ws.Chain.uu (y v) by
        simp only [mul_assoc], hg, mul_one, adj_uu_mul_uu_eq_one]
    · intro i
      show (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) i i = 1
      rw [hform v]
      fin_cases i <;> rfl
    · intro i j hij
      show (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) i j = 0
      rw [hform v]
      revert hij
      fin_cases i <;> fin_cases j <;> intro hij <;> first | rfl | exact absurd hij (by decide)
  · intro v s hs
    show IsUp (adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v)))
    rw [hkey v s hs]
    exact hc.pair.flag v s hs
  · intro v s hs i
    show (adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v))) i i = 1
    rw [hkey v s (hMu v s hs)]
    exact hc.pair.mu v s hs i
  · intro v s hs i
    show (adj (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) * c.r s * (c.n v * UpperTheory.V.Ws.Chain.uu (y v))) i i = _
    rw [hkey v s hs]
    exact hc.res.char v s hs i
  · right
    intro g i j hij hw
    apply hr g i j hij
    intro hm
    apply hw
    rw [Finset.mem_singleton] at hm
    rw [hm]
    decide
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · show SuppM qQ (c.n v * UpperTheory.V.Ws.Chain.uu (y v))
      rw [hform v]
      intro i j hij hw
      revert hij hw
      fin_cases i <;> fin_cases j <;> intro hij hw <;>
        first | rfl | exact absurd rfl hij | exact absurd (by decide) hw
    · show (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) 1 0 = c.n v 1 0
      rw [hform v]
      rfl
    · show (c.n v * UpperTheory.V.Ws.Chain.uu (y v)) 2 0 = y v
      rw [hform v]
      rfl

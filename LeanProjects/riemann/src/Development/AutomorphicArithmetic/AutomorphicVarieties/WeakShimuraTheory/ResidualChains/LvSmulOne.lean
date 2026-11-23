import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Chain.Levi

variable {k : Type} [Field k]

private def Par (X : M4 k) : Prop := ∀ i j : Fin 4, i.1 < 2 → 2 ≤ j.1 → X i j = 0

private def lv (X : M4 k) : M4 k := Matrix.of fun i j => if (i.1 < 2 ↔ j.1 < 2) then X i j else 0

private theorem lv_apply (X : M4 k) (i j : Fin 4) : lv X i j = if (i.1 < 2 ↔ j.1 < 2) then X i j else 0 := rfl

private theorem lv_diag (X : M4 k) (i : Fin 4) : lv X i i = X i i := by
  rw [lv_apply, if_pos Iff.rfl]

end UpperTheory.V.Ws.Chain.Levi

private theorem levi_lemma {k : Type} [Field k] (X : M4 k) :
    adj (UpperTheory.V.Ws.Chain.Levi.lv X) = UpperTheory.V.Ws.Chain.Levi.lv (adj X) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj, UpperTheory.V.Ws.Chain.Levi.lv_apply] <;> rfl

private theorem levi_lv_mul_of_par {k : Type} [Field k] (X Y : M4 k) (hX : UpperTheory.V.Ws.Chain.Levi.Par X)
    (hY : UpperTheory.V.Ws.Chain.Levi.Par Y) :
    UpperTheory.V.Ws.Chain.Levi.lv (X * Y) = UpperTheory.V.Ws.Chain.Levi.lv X * UpperTheory.V.Ws.Chain.Levi.lv Y := by
  have h02 := hX 0 2 (by decide) (by decide)
  have h03 := hX 0 3 (by decide) (by decide)
  have h12 := hX 1 2 (by decide) (by decide)
  have h13 := hX 1 3 (by decide) (by decide)
  have g02 := hY 0 2 (by decide) (by decide)
  have g03 := hY 0 3 (by decide) (by decide)
  have g12 := hY 1 2 (by decide) (by decide)
  have g13 := hY 1 3 (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.V.Ws.Chain.Levi.lv_apply, Matrix.mul_apply, Fin.sum_univ_four,
      h02, h03, h12, h13, g02, g03, g12, g13]

private theorem levi_par_mul {k : Type} [Field k] (X Y : M4 k) (hX : UpperTheory.V.Ws.Chain.Levi.Par X)
    (hY : UpperTheory.V.Ws.Chain.Levi.Par Y) : UpperTheory.V.Ws.Chain.Levi.Par (X * Y) := by
  intro i j hi hj
  rw [Matrix.mul_apply, Fin.sum_univ_four, hY 0 j (by decide) hj, hY 1 j (by decide) hj,
    hX i 2 hi (by decide), hX i 3 hi (by decide)]
  simp

private theorem levi_par_adj {k : Type} [Field k] (X : M4 k) (hX : UpperTheory.V.Ws.Chain.Levi.Par X) :
    UpperTheory.V.Ws.Chain.Levi.Par (adj X) := by
  intro i j hi hj
  have h := hX j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)
  simp [adj, h]

private theorem levi_par_of_apply_eq_zero_of_lt {k : Type} [Field k] (X : M4 k) (hX : ∀ i j : Fin 4, i < j → X i j = 0) :
    UpperTheory.V.Ws.Chain.Levi.Par X := by
  intro i j hi hj
  exact hX i j (Fin.lt_def.2 (by omega))

private theorem levi_lemma_6 {k : Type} [Field k] (X : M4 k) (hX : SuppM nM X) :
    ∀ i j : Fin 4, i < j → X i j = 0 := by
  intro i j hij
  apply hX i j (ne_of_lt hij)
  revert hij
  fin_cases i <;> fin_cases j <;> decide

private theorem suppM_neg_wAl_levi_lv_of_apply_eq_zero_of_lt {k : Type} [Field k] (X : M4 k) (hX : ∀ i j : Fin 4, i < j → X i j = 0) :
    SuppM {-wAl} (UpperTheory.V.Ws.Chain.Levi.lv X) := by
  intro i j hij hw
  rw [UpperTheory.V.Ws.Chain.Levi.lv_apply]
  split_ifs with h
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hX i j hlt
    · exfalso
      revert hgt hw h
      fin_cases i <;> fin_cases j <;> decide
  · rfl

private theorem levi_lv_smul_one {k : Type} [Field k] (c : k) :
    UpperTheory.V.Ws.Chain.Levi.lv (c • (1 : M4 k)) = c • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.Chain.Levi.lv_apply]

private theorem isUp_levi_lv_of_isUp {k : Type} [Field k] (X : M4 k) (hX : IsUp X) :
    IsUp (UpperTheory.V.Ws.Chain.Levi.lv X) := by
  intro i j h
  rw [UpperTheory.V.Ws.Chain.Levi.lv_apply]
  split_ifs
  · exact hX i j h
  · rfl

private theorem levi_lv_adj_mul_mul_of_par {k : Type} [Field k] (A B : M4 k) (hA : UpperTheory.V.Ws.Chain.Levi.Par A)
    (hB : UpperTheory.V.Ws.Chain.Levi.Par B) :
    UpperTheory.V.Ws.Chain.Levi.lv (adj A * B * A) =
      adj (UpperTheory.V.Ws.Chain.Levi.lv A) * UpperTheory.V.Ws.Chain.Levi.lv B * UpperTheory.V.Ws.Chain.Levi.lv A := by
  rw [levi_lv_mul_of_par _ _ (levi_par_mul _ _ (levi_par_adj _ hA) hB) hA, levi_lv_mul_of_par _ _ (levi_par_adj _ hA) hB, levi_lemma]

private theorem isGSp_levi_lv_of_par {k : Type} [Field k] (X : M4 k) (hX : UpperTheory.V.Ws.Chain.Levi.Par X)
    (ν : k) (h : IsGSp ν X) : IsGSp ν (UpperTheory.V.Ws.Chain.Levi.lv X) := by
  unfold IsGSp at h ⊢
  rw [levi_lemma, ← levi_lv_mul_of_par _ _ (levi_par_adj _ hX) hX, h, levi_lv_smul_one]

open UpperTheory.V.Ws.Chain.Levi in
theorem UpperTheory.V.Ws.Chain.levi :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k),
      (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) → ∀ c : PD Φ.ι Γ k, Φ.IsRes a c → Supp nM c.r →
      ∃ c' : PD Φ.ι Γ k, Φ.IsRes a c' ∧ Supp {-wAl} c'.r ∧ (∀ v, SuppM {-wAl} (c'.n v)) ∧ c'.SameAl c := by
  intro O Γ _ _ _ Φ k _ a _ c hc hr
  have hL : ∀ g, ∀ i j : Fin 4, i < j → c.r g i j = 0 := fun g => levi_lemma_6 _ (hr g)
  have hP : ∀ g, Par (c.r g) := fun g => levi_par_of_apply_eq_zero_of_lt _ (hL g)
  have hNL : ∀ v, ∀ i j : Fin 4, i < j → c.n v i j = 0 := fun v => (hc.pair.low v).2.2
  have hN : ∀ v, Par (c.n v) := fun v => levi_par_of_apply_eq_zero_of_lt _ (hNL v)
  let r' : Γ →* M4 k :=
    { toFun := fun g => lv (c.r g)
      map_one' := by
        simp only [map_one]
        simpa using levi_lv_smul_one (1 : k)
      map_mul' := fun x y => by
        simp only [map_mul]
        exact levi_lv_mul_of_par _ _ (hP x) (hP y) }
  have hr' : ∀ g, r' g = lv (c.r g) := fun g => rfl
  have hψ : ∀ v i s, (PD.mk r' (fun v => lv (c.n v))).ψ v i s = c.ψ v i s := by
    intro v i s
    show (adj (lv (c.n v)) * r' s * lv (c.n v)) i i = (adj (c.n v) * c.r s * c.n v) i i
    rw [hr', ← levi_lv_adj_mul_mul_of_par _ _ (hN v) (hP s), lv_diag]
  refine ⟨PD.mk r' (fun v => lv (c.n v)), ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro g
    exact isGSp_levi_lv_of_par _ (hP g) _ (hc.pair.mult g)
  · intro g hg
    show lv (c.r g) = 1
    rw [hc.pair.kill g hg]
    simpa using levi_lv_smul_one (1 : k)
  · intro i j hij
    show lv (c.r Φ.g0) i j = 0
    rw [lv_apply]
    split_ifs
    · exact hc.pair.nrm hij
    · rfl
  · intro v
    refine ⟨isGSp_levi_lv_of_par _ (hN v) _ (hc.pair.low v).1, fun i => ?_, fun i j hij => ?_⟩
    · show lv (c.n v) i i = 1
      rw [lv_diag]
      exact (hc.pair.low v).2.1 i
    · show lv (c.n v) i j = 0
      rw [lv_apply]
      split_ifs
      · exact hNL v i j hij
      · rfl
  · intro v s hs
    show IsUp (adj (lv (c.n v)) * r' s * lv (c.n v))
    rw [hr', ← levi_lv_adj_mul_mul_of_par _ _ (hN v) (hP s)]
    exact isUp_levi_lv_of_isUp _ (hc.pair.flag v s hs)
  · intro v s hs i
    rw [hψ]
    exact hc.pair.mu v s hs i
  · intro g i
    show lv (c.r g) i i = _
    rw [lv_diag]
    exact hc.res.diag g i
  · intro v s hs i
    rw [hψ]
    exact hc.res.char v s hs i
  · right
    intro g
    show SuppM nM (lv (c.r g))
    intro i j hij hw
    exact suppM_neg_wAl_levi_lv_of_apply_eq_zero_of_lt _ (hL g) i j hij (by
      intro hm
      apply hw
      rw [Finset.mem_singleton] at hm
      rw [hm]
      decide)
  · intro i j
    show AdicCont ⊥ (fun g => lv (c.r g) i j)
    simp only [lv_apply]
    split_ifs
    · exact hc.cont i j
    · intro N
      exact IsLocallyConstant.const _
  · intro g
    exact suppM_neg_wAl_levi_lv_of_apply_eq_zero_of_lt _ (hL g)
  · intro v
    exact suppM_neg_wAl_levi_lv_of_apply_eq_zero_of_lt _ (hNL v)
  · refine ⟨fun g => ?_, fun v => ?_⟩
    · show c.r g 1 0 = lv (c.r g) 1 0
      rw [lv_apply, if_pos (by decide)]
    · show c.n v 1 0 = lv (c.n v) 1 0
      rw [lv_apply, if_pos (by decide)]

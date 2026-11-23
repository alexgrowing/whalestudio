import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section
variable {R : Type} [CommRing R]

private theorem rd_adj_mul (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem rd_adj_one : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

private theorem rd_sp {n n' m : M4 R} (h1 : n * m = 1) (h : adj n' * n + adj n * n' = 0) : n' * m ∈ sp4 R := by
  show adj _ = -_
  have e : adj n' = -(adj n * (n' * m)) := by
    have := congrArg (· * m) h
    simp only [add_mul, mul_assoc, h1, mul_one, zero_mul] at this
    exact eq_neg_of_add_eq_zero_left this
  rw [rd_adj_mul, e, mul_neg, ← mul_assoc, ← rd_adj_mul, h1, rd_adj_one, one_mul]

private theorem rd_up_mul {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hX i l hl, zero_mul]
  · rw [hY l j (lt_of_lt_of_le hij (not_lt.1 hl)), mul_zero]

end

section
variable {k : Type} [Field k]

private theorem rd_snd_mul (X Y : M4 (DualNumber k)) :
    (X * Y).map TrivSqZeroExt.snd = X.map TrivSqZeroExt.snd * Y.map TrivSqZeroExt.fst
      + X.map TrivSqZeroExt.fst * Y.map TrivSqZeroExt.snd := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four, TrivSqZeroExt.snd_add,
    DualNumber.snd_mul]
  ring

private theorem rd_fst_mul (X Y : M4 (DualNumber k)) :
    (X * Y).map TrivSqZeroExt.fst = X.map TrivSqZeroExt.fst * Y.map TrivSqZeroExt.fst := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_four, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul]

private theorem rd_snd_adj (X : M4 (DualNumber k)) : (adj X).map TrivSqZeroExt.snd = adj (X.map TrivSqZeroExt.snd) := by
  ext i j
  simp only [adj_apply, Matrix.map_apply, TrivSqZeroExt.snd_smul]

private theorem rd_fst_adj (X : M4 (DualNumber k)) : (adj X).map TrivSqZeroExt.fst = adj (X.map TrivSqZeroExt.fst) := by
  ext i j
  simp only [adj_apply, Matrix.map_apply, TrivSqZeroExt.fst_smul]

private theorem rd_gsp {ν : DualNumber k} (hν : ν.snd = 0) {X : M4 (DualNumber k)} (h : IsGSp ν X) :
    adj (X.map TrivSqZeroExt.snd) * X.map TrivSqZeroExt.fst + adj (X.map TrivSqZeroExt.fst) * X.map TrivSqZeroExt.snd = 0 := by
  rw [← rd_snd_adj, ← rd_fst_adj, ← rd_snd_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij, hν]

private theorem rd_gsp_one {X : M4 (DualNumber k)} (h : IsGSp 1 X) :
    adj (X.map TrivSqZeroExt.fst) * X.map TrivSqZeroExt.fst = 1 := by
  rw [← rd_fst_adj, ← rd_fst_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.redDual :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* DualNumber k) (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ k) (Q : PD Φ.ι Γ (DualNumber k)),
          (∀ x, (a x).snd = 0) → Φ.IsPair a Q → (∀ i j, IsLocallyConstant fun g => Q.r g i j) → (∀ g i j, (Q.r g i j).fst = c.r g i j) → (∀ v i j, (Q.n v i j).fst = c.n v i j) → Supp S Q.r →
          ((fun g => (Q.r g).map TrivSqZeroExt.snd * c.r g⁻¹, fun v => (Q.n v).map TrivSqZeroExt.snd * adj (c.n v)) : (Γ → M4 k) × (Φ.ι → M4 k)) ∈ Φ.Tan S c := by
  intro O Γ _ _ _ _ Φ k _ a S c Q ha hP hlc hr hn hS
  have er : ∀ g, (Q.r g).map TrivSqZeroExt.fst = c.r g := fun g => Matrix.ext (hr g)
  have en : ∀ v, (Q.n v).map TrivSqZeroExt.fst = c.n v := fun v => Matrix.ext (hn v)
  have i1 : ∀ g, c.r g * c.r g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have i2 : ∀ g, c.r g⁻¹ * c.r g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have n1 : ∀ v, adj (c.n v) * c.n v = 1 := fun v => en v ▸ rd_gsp_one (hP.low v).1
  have n2 : ∀ v, c.n v * adj (c.n v) = 1 := fun v => mul_eq_one_comm.1 (n1 v)
  have n3 : ∀ v, adj ((Q.n v).map TrivSqZeroExt.snd) * c.n v + adj (c.n v) * (Q.n v).map TrivSqZeroExt.snd = 0 :=
    fun v => en v ▸ rd_gsp rfl (hP.low v).1
  have hl : IsLocallyConstant fun g => Q.r g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have : ∀ᶠ y in nhds x, ∀ i j, Q.r y i j = Q.r x i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hlc i j).eventually_eq x
    exact this.mono fun y hy => Matrix.ext hy
  refine ⟨?_, fun g => ?_, fun g h => ?_, fun g hg => ?_, ?_, fun g i j hij hw => ?_, fun v => ⟨rd_sp (n2 v) (n3 v), fun i j hij => ?_⟩,
    fun v s hs => ?_⟩
  · have h1 := hl.comp fun X : M4 (DualNumber k) => X.map TrivSqZeroExt.snd
    have h2 := (hl.comp fun X : M4 (DualNumber k) => X.map TrivSqZeroExt.fst).comp_continuous continuous_inv
    have h3 := h1.mul h2
    convert h3 using 1
    funext g
    simp only [Pi.mul_apply, Function.comp_apply, er]
  · exact rd_sp (i1 g) (er g ▸ rd_gsp (ha _) (hP.mult g))
  · show _ * _ = _ * _ + _ * (_ * _) * _
    rw [map_mul, rd_snd_mul, er, er, mul_inv_rev, map_mul, add_mul, mul_assoc, ← mul_assoc (c.r h), i1, one_mul]
    simp only [mul_assoc]
  · show _ * _ = _
    rw [hP.kill g hg]
    have : (1 : M4 (DualNumber k)).map TrivSqZeroExt.snd = 0 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [this, zero_mul]
  · have d1 : ((Q.r Φ.g0).map TrivSqZeroExt.snd).IsDiag := hP.nrm.map rfl
    have d2 : (c.r Φ.g0).IsDiag := er _ ▸ hP.nrm.map rfl
    intro i j hij
    have e := i1 Φ.g0
    rw [← d2.diagonal_diag] at e
    have e1 := congrFun (congrFun e i) i
    have e2 := congrFun (congrFun e i) j
    rw [Matrix.diagonal_mul, Matrix.one_apply_eq] at e1
    rw [Matrix.diagonal_mul, Matrix.one_apply_ne hij] at e2
    have e3 := (mul_eq_zero.1 e2).resolve_left (left_ne_zero_of_mul_eq_one e1)
    show (_ * _ : M4 k) i j = 0
    rw [← d1.diagonal_diag, Matrix.diagonal_mul, e3, mul_zero]
  · show (_ * _ * _ : M4 k) i j = 0
    rw [mul_assoc, i2, mul_one, Matrix.map_apply, hS g i j hij hw]
    rfl
  · show (_ * (_ * _) * _ : M4 k) i j = 0
    rw [mul_assoc, mul_assoc, n1, mul_one, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : i < l
    · rw [adj_apply, ← hn, (hP.low v).2.2 _ _ (Fin.rev_lt_rev.2 hl)]
      simp
    · rw [Matrix.map_apply]
      rcases ((not_lt.1 hl).trans hij).lt_or_eq with h | h
      · rw [(hP.low v).2.2 _ _ h]; simp
      · rw [h, (hP.low v).2.1]; simp
  · have u1 : IsUp ((adj (Q.n v) * Q.r s * Q.n v).map TrivSqZeroExt.snd) := fun i j hij => by
      rw [Matrix.map_apply, hP.flag v s hs i j hij]; rfl
    have u2 : IsUp ((adj (Q.n v) * Q.r s⁻¹ * Q.n v).map TrivSqZeroExt.fst) := fun i j hij => by
      rw [Matrix.map_apply, hP.flag v _ (inv_mem hs) i j hij]; rfl
    have u := rd_up_mul u1 u2
    simp only [rd_snd_mul, rd_fst_mul, rd_snd_adj, rd_fst_adj, er, en] at u
    convert u using 1
    have k1 : ∀ X : M4 k, c.n v * (adj (c.n v) * X) = X := fun X => by rw [← mul_assoc, n2, one_mul]
    have k2 : ∀ X : M4 k, c.r s * (c.r s⁻¹ * X) = X := fun X => by rw [← mul_assoc, i1, one_mul]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, k1, k2, n1, mul_one, eq_neg_of_add_eq_zero_left (n3 v)]
    abel

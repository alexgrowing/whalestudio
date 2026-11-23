import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

private theorem add_lt {K : Type} [NormedField K] [IsUltrametricDist K] {a b : K} {M : ℝ} (ha : ‖a‖ < M) (hb : ‖b‖ < M) :
    ‖a + b‖ < M := (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

private theorem sub_lt {K : Type} [NormedField K] [IsUltrametricDist K] {a b : K} {M : ℝ} (ha : ‖a‖ < M) (hb : ‖b‖ < M) :
    ‖a - b‖ < M := by
  rw [sub_eq_add_neg]; exact add_lt ha (by rwa [norm_neg])

private theorem sum_lt {K : Type} [NormedField K] [IsUltrametricDist K] (f : Fin 4 → K) {M : ℝ} (h : ∀ k, ‖f k‖ < M) :
    ‖∑ k, f k‖ < M := by
  rw [Fin.sum_univ_four]; exact add_lt (add_lt (add_lt (h _) (h _)) (h _)) (h _)

private theorem block_of_intertwine {K : Type} [NormedField K] [IsUltrametricDist K] (X X' u : M4 K) (d : Fin 4 → K)
    (hX : ∀ i j, ‖X i j - Matrix.diagonal d i j‖ < 1) (hX' : ∀ i j, ‖X' i j - Matrix.diagonal d i j‖ < 1)
    (hb : IsBlock X) (hb' : IsBlock X') (hd : ∀ i j, lamW i ≠ lamW j → 1 ≤ ‖d i - d j‖) (h : u * X = X' * u) : IsBlock u := by
  classical
  obtain ⟨⟨i, j⟩, hij, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun p : Fin 4 × Fin 4 => lamW p.1 ≠ lamW p.2)
    (fun p => ‖u p.1 p.2‖) ⟨(0, 1), by decide⟩
  have hij' : lamW i ≠ lamW j := (Finset.mem_filter.1 hij).2
  have hm : ∀ a b, lamW a ≠ lamW b → ‖u a b‖ ≤ ‖u i j‖ := fun a b hab =>
    hmax (a, b) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩)
  by_cases h0 : u i j = 0
  · intro a b hab
    have := hm a b hab
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.1 this
  exfalso
  have hpos : 0 < ‖u i j‖ := norm_pos_iff.2 h0
  have e : (d i - d j) * u i j = (u * (X - Matrix.diagonal d)) i j - ((X' - Matrix.diagonal d) * u) i j := by
    rw [Matrix.mul_sub, Matrix.sub_mul, h, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  have t1 : ‖(u * (X - Matrix.diagonal d)) i j‖ < ‖u i j‖ := by
    rw [Matrix.mul_apply]
    refine sum_lt _ fun k => ?_
    by_cases hk : lamW k = lamW j
    · rw [norm_mul]
      have h1 := hm i k (hk ▸ hij')
      have h2 := hX k j
      rw [Matrix.sub_apply]
      calc _ ≤ ‖u i j‖ * ‖X k j - Matrix.diagonal d k j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < ‖u i j‖ := mul_lt_of_lt_one_right hpos h2
    · have hkj : k ≠ j := fun hh => hk (hh ▸ rfl)
      rw [Matrix.sub_apply, hb k j hk, Matrix.diagonal_apply_ne _ hkj]
      simpa using h0
  have t2 : ‖((X' - Matrix.diagonal d) * u) i j‖ < ‖u i j‖ := by
    rw [Matrix.mul_apply]
    refine sum_lt _ fun k => ?_
    by_cases hk : lamW i = lamW k
    · rw [norm_mul]
      have h1 := hm k j (hk ▸ hij')
      have h2 := hX' i k
      rw [Matrix.sub_apply]
      calc _ ≤ ‖X' i k - Matrix.diagonal d i k‖ * ‖u i j‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ < ‖u i j‖ := mul_lt_of_lt_one_left hpos h2
    · have hkj : i ≠ k := fun hh => hk (hh ▸ rfl)
      rw [Matrix.sub_apply, hb' i k hk, Matrix.diagonal_apply_ne _ hkj]
      simpa using h0
  have t3 := sub_lt t1 t2
  rw [← e, norm_mul] at t3
  exact absurd t3 (not_lt.2 (le_mul_of_one_le_left hpos.le (hd i j hij')))

private theorem ne_of_close {K : Type} [NormedField K] [IsUltrametricDist K] {a b a' b' : K} (ha : ‖a - a'‖ < 1)
    (hb : ‖b - b'‖ < 1) (h : 1 ≤ ‖a' - b'‖) : a ≠ b := by
  rintro rfl
  have := sub_lt hb ha
  rw [show a - b' - (a - a') = a' - b' by ring] at this
  exact absurd this (not_lt.2 h)

private theorem corner_zero {K : Type} [Field K] (H H' u : M4 K) (hu : IsBlock u) (h02 : H 0 2 = 0) (h20 : H 2 0 = 0)
    (h02' : H' 0 2 = 0) (h20' : H' 2 0 = 0) (n1 : H 2 2 ≠ H' 0 0) (n2 : H 0 0 ≠ H' 2 2) (h : u * H = H' * u) :
    u 0 2 = 0 ∧ u 2 0 = 0 := by
  have e1 := congrFun (congrFun h 0) 2
  have e2 := congrFun (congrFun h 2) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_four, hu 0 1 (by decide), hu 0 3 (by decide), hu 1 2 (by decide),
    hu 3 2 (by decide), hu 2 1 (by decide), hu 2 3 (by decide), hu 1 0 (by decide), hu 3 0 (by decide), h02, h20, h02', h20'] at e1 e2
  constructor
  · have : u 0 2 * (H 2 2 - H' 0 0) = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 n1)
  · have : u 2 0 * (H 0 0 - H' 2 2) = 0 := by linear_combination e2
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 n2)

private theorem gsp_of_conj {K H : Type} [Field K] [Group H] (r r' : H →* M4 K) (ν : H → K) (hν : ∀ g, ν g ≠ 0)
    (hr : ∀ g, IsGSp (ν g) (r g)) (hr' : ∀ g, IsGSp (ν g) (r' g)) (hI : Irr r) (u : M4 K) (h : ∀ g, u * r g = r' g * u) :
    ∃ a, IsGSp a u := by
  obtain ⟨gm, -, -, -, -, -, gi, -⟩ := grp K
  have c1 : ∀ g, r g * (adj u * u) = (adj u * u) * r g := by
    intro g
    have a1 : adj (r g⁻¹) = ν g⁻¹ • r g := gi _ _ _ (hr _) (by rw [← map_mul, inv_mul_cancel, map_one])
    have a2 : adj (r' g⁻¹) = ν g⁻¹ • r' g := gi _ _ _ (hr' _) (by rw [← map_mul, inv_mul_cancel, map_one])
    have a3 := congrArg adj (h g⁻¹)
    rw [gm, gm, a1, a2, smul_mul_assoc, mul_smul_comm] at a3
    have a4 := smul_right_injective _ (hν g⁻¹) a3
    rw [← mul_assoc, a4, mul_assoc, ← h, mul_assoc]
  have c2 : ∀ Y : M4 K, Y * (adj u * u) = (adj u * u) * Y := by
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range r) := by rw [hI]; trivial
    induction hY using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact c1 g
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul a x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
  obtain ⟨a, ha⟩ := (Matrix.mem_range_scalar_iff_commute_single' (M := adj u * u)).2 fun i j => c2 _
  refine ⟨a, ?_⟩
  rw [IsGSp, ← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

private theorem torus_of_gsp {K : Type} [Field K] (u : (M4 K)ˣ) (a : K) (hg : IsGSp a (u : M4 K)) (hu : IsBlock (u : M4 K))
    (h02 : (u : M4 K) 0 2 = 0) (h20 : (u : M4 K) 2 0 = 0) :
    ∃ t : Kˣ × Kˣ, ∀ X X' : M4 K, u * X = X' * u → X' = tconj t X := by
  have z01 := hu 0 1 (by decide)
  have z03 := hu 0 3 (by decide)
  have z12 := hu 1 2 (by decide)
  have z32 := hu 3 2 (by decide)
  have z21 := hu 2 1 (by decide)
  have z23 := hu 2 3 (by decide)
  have z10 := hu 1 0 (by decide)
  have z30 := hu 3 0 (by decide)
  have row : ∀ i, (∀ j, j ≠ i → (u : M4 K) i j = 0) → (u : M4 K) i i ≠ 0 := by
    intro i hi h0
    have := congrFun (congrFun u.mul_inv i) i
    rw [Matrix.mul_apply, Finset.sum_eq_zero, Matrix.one_apply_eq] at this
    · exact zero_ne_one this
    · intro j _
      by_cases hj : j = i
      · rw [hj, h0, zero_mul]
      · rw [hi j hj, zero_mul]
  have n0 := row 0 (by intro j hj; fin_cases j <;> simp_all)
  have n2 := row 2 (by intro j hj; fin_cases j <;> simp_all)
  have e02 := congrFun (congrFun hg 0) 2
  have e20 := congrFun (congrFun hg 2) 0
  have e00 := congrFun (congrFun hg 0) 0
  have e22 := congrFun (congrFun hg 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, z01, z03, z12, z32, z21, z23, z10, z30, h02, h20, n0, n2]
    at e02 e20 e00 e22
  have n1 := row 1 (by intro j hj; fin_cases j <;> simp_all)
  have n3 := row 3 (by intro j hj; fin_cases j <;> simp_all)
  have hd : (u : M4 K) = Matrix.diagonal fun i => (u : M4 K) i i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z01, z03, z12, z32, z21, z23, z10, z30, h02, h20, e02, e20]
  refine ⟨(Units.mk0 _ (div_ne_zero n2 n3), Units.mk0 _ (div_ne_zero n1 n3)), fun X X' h => ?_⟩
  have hw : ∀ i j, (wv (Units.mk0 _ (div_ne_zero n2 n3), Units.mk0 _ (div_ne_zero n1 n3)) (wt i j) : K) * (u : M4 K) j j =
      (u : M4 K) i i := by
    have e0 : (u : M4 K) 0 0 = (u : M4 K) 1 1 * (u : M4 K) 2 2 / (u : M4 K) 3 3 := by
      field_simp; linear_combination e00 - e22
    intro i j
    fin_cases i <;> fin_cases j <;> simp [wv, wt, lamW, muW, e0] <;> field_simp
  have hn : ∀ j, (u : M4 K) j j ≠ 0 := by intro j; fin_cases j <;> assumption
  ext i j
  have := congrFun (congrFun h i) j
  rw [hd, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  apply mul_right_cancel₀ (hn j)
  rw [← this, tconj, Matrix.of_apply, ← hw i j]
  ring

private theorem norm_le_one_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_unit {l : ℕ} [Fact l.Prime] (c : Coef l) {x : c.O} (hx : IsUnit x) :
    ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := by
  have hle : ∀ y : c.O, ‖(y : PadicAlgCl l)‖ ≤ 1 := fun y =>
    norm_le_one_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c.O.val)
  obtain ⟨u, rfl⟩ := hx
  show ‖((u : c.O) : PadicAlgCl l)‖ = 1
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := hle u
  have h3 := hle (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

private theorem norm_sub_of_res {l : ℕ} [Fact l.Prime] (c : Coef l) {x y : c.O} (h : residue c.O x ≠ residue c.O y) :
    ‖algebraMap c.O (PadicAlgCl l) x - algebraMap c.O (PadicAlgCl l) y‖ = 1 := by
  rw [← map_sub]
  refine norm_unit c ?_
  rw [← residue_ne_zero_iff_isUnit, map_sub]
  exact sub_ne_zero.2 h

end SlopeTestRemainingChoices

theorem UpperTheory.V.GradeZeroInterpolatingElement.conjTorus :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r r', D.EPt r → D.EPt r' → Irr r → IsConj4 r r' → ∃ t, ∀ g, r' g = tconj t (r g) := by
  intro Ω _ _ _ l _ c D hD r r' hr hr' hI ⟨u, hu⟩
  have hint : ∀ g, (u : M4 (PadicAlgCl l)) * r g = r' g * u := fun g => by
    rw [hu g, Units.inv_mul_cancel_right]
  obtain ⟨hM, -, hN, -⟩ := ptIn D hD _ r hr
  obtain ⟨hM', -, hN', -⟩ := ptIn D hD _ r' hr'
  obtain ⟨-, hc, -⟩ := eptInt D hD r hr
  obtain ⟨-, hc', -⟩ := eptInt D hD r' hr'
  obtain ⟨-, hT, -, -, -, -, -, -, -, hph, -⟩ := facts D hD
  have hdiag : ∀ g, D.r0E g = Matrix.diagonal fun i => algebraMap c.O (PadicAlgCl l) (D.ps i g : c.O) := fun g => by
    ext i j
    show algebraMap c.O (PadicAlgCl l) (Matrix.diagonal (fun i => (D.ps i g : c.O)) i j) = _
    by_cases h : i = j
    · subst h; rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]
  have hbar : ∀ g i, D.rbar g i i = Raw.bar (D.ps i) g := fun g i => by
    show residue c.O (Matrix.diagonal (fun i => (D.ps i g : c.O)) i i) = _
    rw [Matrix.diagonal_apply_eq]
  have hB : IsBlock (u : M4 (PadicAlgCl l)) := by
    refine block_of_intertwine (r D.ph) (r' D.ph) u _ (fun i j => hdiag D.ph ▸ hc _ i j) (fun i j => hdiag D.ph ▸ hc' _ i j)
      hN.1 hN'.1 (fun i j hij => (norm_sub_of_res c ?_).ge) (hint _)
    have := (hT l (Finset.mem_insert_self _ _)).2.2 i j hij
    rw [← hbar, ← hbar, ← hph, hbar, hbar] at this
    exact this
  have hth : ∀ g, ‖algebraMap c.O (PadicAlgCl l) (D.th g : c.O)‖ = 1 := fun g => norm_unit c (Units.isUnit _)
  have hH : ∀ s : G ℚ Ω →* M4 (PadicAlgCl l), (∀ g i j, ‖s g i j - D.r0E g i j‖ < 1) → ∀ i,
      ‖D.hEl s i i - algebraMap c.O (PadicAlgCl l) ((D.ps i D.g0 : c.O) + (D.th D.g0 : c.O) * (D.ps i D.g0⁻¹ : c.O))‖ < 1 := by
    intro s hs i
    have h1 := hs D.g0 i i
    have h2 := hs D.g0⁻¹ i i
    rw [hdiag, Matrix.diagonal_apply_eq] at h1 h2
    have h3 : ‖algebraMap c.O (PadicAlgCl l) (D.th D.g0 : c.O) *
        (s D.g0⁻¹ i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0⁻¹ : c.O))‖ < 1 := by
      rw [norm_mul, hth, one_mul]; exact h2
    convert add_lt h1 h3 using 2
    rw [Raw.hEl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  have hne : residue c.O ((D.ps 0 D.g0 : c.O) + (D.th D.g0 : c.O) * (D.ps 0 D.g0⁻¹ : c.O)) ≠
      residue c.O ((D.ps 2 D.g0 : c.O) + (D.th D.g0 : c.O) * (D.ps 2 D.g0⁻¹ : c.O)) := by
    have p0 : D.ps 0 = D.th := rfl
    have p2 : D.ps 2 = D.al := rfl
    have q0 : (D.th D.g0 : c.O) * (D.th D.g0⁻¹ : c.O) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have q1 : (D.th D.g0 : c.O) = (D.al D.g0 : c.O) * (D.Psi D.g0 : c.O) := rfl
    have q2 : (D.al D.g0 : c.O) * (D.al D.g0⁻¹ : c.O) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [p0, p2, q0, q1, mul_right_comm, q2, one_mul, map_add, map_add, map_mul, map_one]
    intro h
    have : (Raw.bar D.al D.g0 - 1) * (Raw.bar D.Psi D.g0 - 1) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).elim (sub_ne_zero.2 hD.genElt_alpha) (sub_ne_zero.2 hD.genElt_Psi)
  obtain ⟨h02, h20⟩ := corner_zero (D.hEl r) (D.hEl r') u hB hN.2.1 hN.2.2 hN'.2.1 hN'.2.2
    (ne_of_close (hH r hc 2) (hH r' hc' 0) (norm_sub_of_res c hne.symm).ge)
    (ne_of_close (hH r hc 0) (hH r' hc' 2) (norm_sub_of_res c hne).ge)
    (by rw [Raw.hEl, Raw.hEl, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hint, hint])
  obtain ⟨a, ha⟩ := gsp_of_conj r r' _ (fun g => norm_ne_zero_iff.1 (by rw [hth g]; exact one_ne_zero)) hM hM' hI u hint
  obtain ⟨t, ht⟩ := torus_of_gsp u a ha hB h02 h20
  exact ⟨t, fun g => ht _ _ (hint g)⟩

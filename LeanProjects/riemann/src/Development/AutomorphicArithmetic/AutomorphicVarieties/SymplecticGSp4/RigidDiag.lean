import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem block_of_comm {K : Type} [NormedField K] [IsUltrametricDist K] (M X : M4 K) (d : Fin 4 → K)
    (hM : ∀ i j, ‖M i j - Matrix.diagonal d i j‖ < 1) (hd : ∀ i j, lamW i ≠ lamW j → ‖d i - d j‖ = 1)
    (hb : IsBlock M) (hX : IsBlock (X * M - M * X)) : IsBlock X := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4 × Fin 4))
    (fun p => ‖M p.1 p.2 - Matrix.diagonal d p.1 p.2‖) Finset.univ_nonempty
  obtain ⟨⟨i, j⟩, hq, hm⟩ := Finset.exists_max_image
    (Finset.univ.filter fun q : Fin 4 × Fin 4 => lamW q.1 ≠ lamW q.2) (fun q => ‖X q.1 q.2‖) ⟨(0, 1), by decide⟩
  have hij : lamW i ≠ lamW j := (Finset.mem_filter.1 hq).2
  have hm' : ∀ a b, lamW a ≠ lamW b → ‖X a b‖ ≤ ‖X i j‖ := fun a b h =>
    hm (a, b) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  set ρ := ‖M p.1 p.2 - Matrix.diagonal d p.1 p.2‖ with hρ
  have hρ1 : ρ < 1 := hM _ _
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  obtain ⟨N, hN⟩ : ∃ N, N = M - Matrix.diagonal d := ⟨_, rfl⟩
  have hNρ : ∀ a b, ‖N a b‖ ≤ ρ := fun a b => by
    rw [hN]; exact hp (a, b) (Finset.mem_univ _)
  have hNb : IsBlock N := fun a b h => by
    have : a ≠ b := fun e => h (by rw [e])
    rw [hN, Matrix.sub_apply, hb a b h, Matrix.diagonal_apply_ne _ this, sub_zero]
  have hMN : M = N + Matrix.diagonal d := by rw [hN, sub_add_cancel]
  have h0 := hX i j hij
  rw [hMN, mul_add, add_mul] at h0
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at h0
  have h1 : X i j * (d i - d j) = (X * N) i j + -(N * X) i j := by linear_combination -h0
  have hx0 := norm_nonneg (X i j)
  have h2 : ‖(X * N) i j‖ ≤ ‖X i j‖ * ρ := by
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    by_cases hk : lamW k = lamW j
    · rw [norm_mul]
      exact mul_le_mul (hm' i k (by rw [hk]; exact hij)) (hNρ _ _) (norm_nonneg _) hx0
    · rw [hNb k j hk, mul_zero, norm_zero]; positivity
  have h3 : ‖-(N * X) i j‖ ≤ ‖X i j‖ * ρ := by
    rw [norm_neg, Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    by_cases hk : lamW i = lamW k
    · rw [norm_mul, mul_comm]
      exact mul_le_mul (hm' k j (by rw [← hk]; exact hij)) (hNρ _ _) (norm_nonneg _) hx0
    · rw [hNb i k hk, zero_mul, norm_zero]; positivity
  have h4 : ‖X i j‖ ≤ ‖X i j‖ * ρ := by
    calc ‖X i j‖ = ‖X i j * (d i - d j)‖ := by rw [norm_mul, hd i j hij, mul_one]
      _ ≤ _ := by rw [h1]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 h3)
  have h5 : ‖X i j‖ ≤ 0 := by nlinarith
  intro a b h
  exact norm_le_zero_iff.1 ((hm' a b h).trans h5)

private theorem diag_of_comm {K : Type} [Field K] (X h : M4 K) (hX : X ∈ sp4 K) (hb : IsBlock X)
    (h02 : h 0 2 = 0) (h20 : h 2 0 = 0) (hne : h 0 0 ≠ h 2 2)
    (c02 : (X * h - h * X) 0 2 = 0) (c20 : (X * h - h * X) 2 0 = 0) :
    ∃ a b : K, ∀ (Y : M4 K) i j, (X * Y - Y * X) i j = (a * ((wt i j).1 : K) + b * ((wt i j).2 : K)) * Y i j := by
  have hs : ∀ i j, (sgn i * sgn j) • X j.rev i.rev = -X i j := fun i j => congrFun (congrFun hX i) j
  have z01 := hb 0 1 (by decide)
  have z03 := hb 0 3 (by decide)
  have z10 := hb 1 0 (by decide)
  have z12 := hb 1 2 (by decide)
  have z21 := hb 2 1 (by decide)
  have z23 := hb 2 3 (by decide)
  have z30 := hb 3 0 (by decide)
  have z32 := hb 3 2 (by decide)
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z10, z12, z21, z23, z30, z32, h02, h20] at c02 c20
  have z02 : X 0 2 = 0 := by
    have : X 0 2 * (h 0 0 - h 2 2) = 0 := by linear_combination -c02
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have z20 : X 2 0 = 0 := by
    have : X 2 0 * (h 0 0 - h 2 2) = 0 := by linear_combination c20
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have z13 : X 1 3 = 0 := by simpa [sgn, Fin.rev, z02] using hs 0 2
  have z31 : X 3 1 = 0 := by simpa [sgn, Fin.rev, z20] using hs 2 0
  have z33 : X 3 3 = -X 0 0 := by simpa [sgn, Fin.rev] using hs 0 0
  have z22 : X 2 2 = -X 1 1 := by simpa [sgn, Fin.rev] using hs 1 1
  refine ⟨X 0 0 - X 1 1, X 0 0 + X 1 1, fun Y i j => ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z10, z12, z21, z23, z30, z32, z02, z20, z13, z31, z33, z22, wt, lamW, muW] <;> ring

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖algebraMap c.O (PadicAlgCl l) x‖ ≤ 1 :=
  norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)

private theorem norm_eq_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : residue c.O x ≠ 0) :
    ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := by
  obtain ⟨u, rfl⟩ := (residue_ne_zero_iff_isUnit x).1 hx
  have h1 : ‖algebraMap c.O (PadicAlgCl l) u‖ * ‖algebraMap c.O (PadicAlgCl l) (u⁻¹ : c.Oˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h2 := norm_le_one c u
  have h3 := norm_le_one c (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg (algebraMap c.O (PadicAlgCl l) u)
  nlinarith

theorem UpperTheory.V.GradeZeroInterpolatingElement.rigidDiag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → D.RigidAt r → ∀ r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l)), D.PtIn _ r' → (∀ g i j, (r' g i j).fst = r g i j) → ∃ a b : PadicAlgCl l, ∀ g i j, (r' g i j).snd = (a * ((wt i j).1 : PadicAlgCl l) + b * ((wt i j).2 : PadicAlgCl l)) * r g i j := by
  intro Ω _ _ _ l _ c D hD r hr hrig r' hr' hfst
  obtain ⟨X, hX, hsnd⟩ := hrig r' hr' hfst
  obtain ⟨-, hcl, -⟩ := eptInt D hD r hr
  obtain ⟨-, -, ⟨hb, h02, h20⟩, -⟩ := ptIn D hD _ r hr
  obtain ⟨-, -, ⟨hb', h02', h20'⟩, -⟩ := ptIn D hD _ r' hr'
  obtain ⟨-, hsg, -, -, -, -, -, -, -, hph, -⟩ := facts D hD
  have hr0 : ∀ g, D.r0E g = Matrix.diagonal fun i => algebraMap c.O (PadicAlgCl l) (D.ps i g) := fun g => by
    ext i j
    show algebraMap c.O (PadicAlgCl l) (Matrix.diagonal (fun i => (D.ps i g : c.O)) i j) = _
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq]
    · simp only [Matrix.diagonal_apply_ne _ h, map_zero]
  have hbar : ∀ i, Raw.bar (D.ps i) D.ph = Raw.bar (D.ps i) (D.sg l) := fun i => by
    have := congrFun (congrFun hph i) i
    change residue c.O (Matrix.diagonal (fun i => (D.ps i D.ph : c.O)) i i) =
      residue c.O (Matrix.diagonal (fun i => (D.ps i (D.sg l) : c.O)) i i) at this
    simpa only [Matrix.diagonal_apply_eq] using this
  have hXb : IsBlock X := by
    refine block_of_comm (r D.ph) X (fun i => algebraMap c.O (PadicAlgCl l) (D.ps i D.ph))
      (fun i j => by rw [← hr0]; exact hcl _ i j) (fun i j h => ?_) hb fun i j h => ?_
    · rw [← map_sub]
      refine norm_eq_one c _ ?_
      rw [map_sub, sub_ne_zero]
      have := (hsg l (Finset.mem_insert_self _ _)).2.2 i j h
      rwa [← hbar, ← hbar] at this
    · rw [← hsnd, hb' i j h]; rfl
  have hh : ∀ i j, (D.hEl r' i j).snd = (X * D.hEl r - D.hEl r * X) i j := fun i j => by
    have e : X * D.hEl r - D.hEl r * X = (X * r D.g0 - r D.g0 * X) +
        algebraMap c.O (PadicAlgCl l) (D.th D.g0) • (X * r D.g0⁻¹ - r D.g0⁻¹ * X) := by
      simp only [Raw.hEl, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, Matrix.add_apply, Matrix.smul_apply, ← hsnd, ← hsnd, Raw.hEl, Matrix.add_apply, Matrix.smul_apply,
      TrivSqZeroExt.snd_add, smul_eq_mul, smul_eq_mul, ← Algebra.smul_def, ← Algebra.smul_def]
    rfl
  have hne : D.hEl r 0 0 ≠ D.hEl r 2 2 := by
    intro he
    have hi : ∀ i, ‖D.hEl r i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0 + D.th D.g0 * D.ps i D.g0⁻¹)‖ < 1 := fun i => by
      have a1 := hcl D.g0 i i
      have a2 := hcl D.g0⁻¹ i i
      rw [hr0, Matrix.diagonal_apply_eq] at a1 a2
      have e : D.hEl r i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0 + D.th D.g0 * D.ps i D.g0⁻¹) =
          (r D.g0 i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0)) + algebraMap c.O (PadicAlgCl l) (D.th D.g0) *
            (r D.g0⁻¹ i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0⁻¹)) := by
        rw [Raw.hEl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a1 ?_)
      rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one c _) (norm_nonneg _) a2
    have e : ((D.al D.g0 : c.O) - 1) * ((D.Psi D.g0 : c.O) - 1) =
        (D.ps 0 D.g0 + D.th D.g0 * D.ps 0 D.g0⁻¹) - (D.ps 2 D.g0 + D.th D.g0 * D.ps 2 D.g0⁻¹) := by
      have p0 : D.ps 0 = D.th := rfl
      have p2 : D.ps 2 = D.al := rfl
      have t : (D.th D.g0 : c.O) = D.al D.g0 * D.Psi D.g0 := rfl
      have u1 : (D.th D.g0 : c.O) * D.th D.g0⁻¹ = 1 := by rw [map_inv, Units.mul_inv]
      have u2 : (D.al D.g0 : c.O) * D.al D.g0⁻¹ = 1 := by rw [map_inv, Units.mul_inv]
      rw [p0, p2, u1, t]
      linear_combination (D.Psi D.g0 : c.O) * u2
    have n1 : ‖algebraMap c.O (PadicAlgCl l) (((D.al D.g0 : c.O) - 1) * ((D.Psi D.g0 : c.O) - 1))‖ = 1 := by
      refine norm_eq_one c _ ?_
      rw [map_mul, map_sub, map_sub, map_one]
      exact mul_ne_zero (sub_ne_zero.2 hD.genElt_alpha) (sub_ne_zero.2 hD.genElt_Psi)
    rw [e, map_sub] at n1
    have a1 := hi 0
    have a2 := hi 2
    rw [← he] at a2
    rw [← norm_neg] at a1
    have a3 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a1 a2)
    rw [neg_sub, sub_add_sub_cancel, n1] at a3
    exact lt_irrefl _ a3
  obtain ⟨a, b, hab⟩ := diag_of_comm X (D.hEl r) hX hXb h02 h20 hne (by rw [← hh, h02']; rfl) (by rw [← hh, h20']; rfl)
  exact ⟨a, b, fun g i j => by rw [hsnd, hab]⟩

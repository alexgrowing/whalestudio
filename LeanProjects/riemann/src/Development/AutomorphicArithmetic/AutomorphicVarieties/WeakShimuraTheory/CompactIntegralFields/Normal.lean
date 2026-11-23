import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.HenselDiag

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section
variable {R : Type} [CommRing R]

private theorem adj_mul' (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem adj_adj' (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem adj_diag' (d : Fin 4 → R) : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal]

private theorem adj_sub_one (X : M4 R) : adj (X - 1) = adj X - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem unit_of_sub [IsLocalRing R] {x y : R} (hy : IsUnit y) (h : x - y ∈ maximalIdeal R) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal R := (mem_maximalIdeal x).mpr hx
  have hy' : y ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ hx' h
    rwa [sub_sub_cancel] at this
  exact (mem_maximalIdeal y).mp hy' hy

private def sg (R : Type) [CommRing R] : Fin 4 → R := ![1, -1, 1, -1]

private theorem sg_sq (i : Fin 4) : sg R i * sg R i = 1 := by fin_cases i <;> simp [sg]

private theorem sg_ne (i j : Fin 4) (h : lamW i ≠ lamW j) : sg R i * sg R j = -1 := by
  fin_cases i <;> fin_cases j <;> simp [sg, lamW] at h ⊢

private theorem sg_eq (i j : Fin 4) (h : lamW i = lamW j) : sg R i = sg R j := by
  fin_cases i <;> fin_cases j <;> simp [sg, lamW] at h ⊢

end

theorem UpperTheory.V.Ws.normal :
    ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C] (ν : C) (g : M4 C), IsUnit (2 : C) → IsGSp ν g →
      (∀ i j, i ≠ j → g i j ∈ maximalIdeal C) → (∀ i j, i ≠ j → IsUnit (g i i - g j j)) → IsUnit ν →
      ∃ u : M4 C, IsGSp 1 u ∧ (∀ i j, (u - 1) i j ∈ maximalIdeal C) ∧ (adj u * g * u).IsDiag ∧ (IsBlock g → IsBlock u) := by
  intro C _ _ _ ν g h2u hg hoff hdiff hν
  haveI : HenselianLocalRing C :=
    { (inferInstance : IsLocalRing C) with
      is_henselian := fun f hf a₀ h₁ h₂ =>
        (IsAdicComplete.henselianRing C (maximalIdeal C)).is_henselian f hf a₀ h₁
          (h₂.map (Ideal.Quotient.mk _)) }
  obtain ⟨u, d, hu1, hgu, hdg, huniq⟩ := UpperTheory.V.AlgebraTools.henselDiag C (Fin 4) g hoff hdiff
  have hg' : adj g * g = ν • 1 := hg
  have mulL : ∀ X Y : M4 C, (∀ i j, X i j ∈ maximalIdeal C) →
      ∀ i j, (X * Y) i j ∈ maximalIdeal C := by
    intro X Y hX i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hX i k)
  have mulR : ∀ X Y : M4 C, (∀ i j, Y i j ∈ maximalIdeal C) →
      ∀ i j, (X * Y) i j ∈ maximalIdeal C := by
    intro X Y hY i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hY k j)
  have adjM : ∀ X : M4 C, (∀ i j, X i j ∈ maximalIdeal C) →
      ∀ i j, adj X i j ∈ maximalIdeal C := by
    intro X hX i j
    rw [adj_apply, zsmul_eq_mul]
    exact Ideal.mul_mem_left _ _ (hX _ _)
  have hW1 : ∀ i j, (adj u * u - 1) i j ∈ maximalIdeal C := by
    have e : adj u * u - 1 = adj (u - 1) * (u - 1) + adj (u - 1) + (u - 1) := by
      rw [adj_sub_one]
      noncomm_ring
    intro i j
    rw [e, Matrix.add_apply, Matrix.add_apply]
    exact Ideal.add_mem _ (Ideal.add_mem _ (mulL _ _ (adjM _ hu1) i j) (adjM _ hu1 i j)) (hu1 i j)
  have hWu : ∀ i, IsUnit ((adj u * u) i i) := fun i =>
    unit_of_sub isUnit_one (by
      have := hW1 i i
      rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this)
  have hkey : ν • (adj u * u) = adj (Matrix.diagonal d) * (adj u * u) * Matrix.diagonal d := by
    have e1 : adj u * adj g = adj (Matrix.diagonal d) * adj u := by
      rw [← adj_mul', ← adj_mul', hgu]
    calc ν • (adj u * u) = adj u * (adj g * g) * u := by
          rw [hg']
          simp [Matrix.mul_smul, Matrix.smul_mul]
      _ = (adj u * adj g) * (g * u) := by simp only [Matrix.mul_assoc]
      _ = adj (Matrix.diagonal d) * adj u * (u * Matrix.diagonal d) := by rw [e1, hgu]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hent : ∀ i j, ν * (adj u * u) i j = d i.rev * (adj u * u) i j * d j := by
    intro i j
    have := congrFun (congrFun hkey i) j
    rw [adj_diag'] at this
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    exact this
  have hdd : ∀ i, d i.rev * d i = ν := by
    intro i
    have h0 : (adj u * u) i i * (d i.rev * d i - ν) = 0 := by
      linear_combination (-1 : C) * hent i i
    exact sub_eq_zero.mp ((hWu i).mul_right_eq_zero.mp h0)
  have hdu : ∀ i, IsUnit (d i) := fun i => by
    have : IsUnit (d i.rev * d i) := by rw [hdd i]; exact hν
    exact isUnit_of_mul_isUnit_right this
  have hoffW : ∀ i j, i ≠ j → (adj u * u) i j = 0 := by
    intro i j hij
    have h0 : (adj u * u) i j * (d i.rev * d j - ν) = 0 := by
      linear_combination (-1 : C) * hent i j
    have hu : IsUnit (d i.rev * d j - ν) := by
      rw [← hdd i, ← mul_sub]
      refine (hdu _).mul ?_
      refine unit_of_sub (hdiff j i (Ne.symm hij)) ?_
      have := Ideal.sub_mem _ (hdg j) (hdg i)
      convert this using 1
      ring
    exact hu.mul_left_eq_zero.mp h0
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → C, ∀ i, w i = (adj u * u) i i := ⟨_, fun _ => rfl⟩
  have hWd : adj u * u = Matrix.diagonal w := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hw]
    · rw [hoffW i j hij, Matrix.diagonal_apply_ne _ hij]
  have hwu : ∀ i, IsUnit (w i) := fun i => by rw [hw]; exact hWu i
  have hwm : ∀ i, w i - 1 ∈ maximalIdeal C := fun i => by
    have := hW1 i i
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, ← hw] at this
  have hwrev : ∀ i, w i.rev = w i := by
    have h : adj (adj u * u) = adj u * u := by rw [adj_mul', adj_adj']
    rw [hWd, adj_diag'] at h
    intro i
    have := congrFun (congrFun h i) i
    simpa using this
  have h21 : w 2 = w 1 := by simpa [Fin.rev] using hwrev 1
  have h30 : w 3 = w 0 := by simpa [Fin.rev] using hwrev 0
  obtain ⟨a, ha⟩ : ∃ a, a * w 1 = 1 := ⟨_, (hwu 1).val_inv_mul⟩
  obtain ⟨b, hb⟩ : ∃ b, b * w 0 = 1 := ⟨_, (hwu 0).val_inv_mul⟩
  have ha1 : a - 1 ∈ maximalIdeal C := by
    have e : a - 1 = -(a * (w 1 - 1)) := by linear_combination ha
    rw [e]
    exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (hwm 1))
  have hb1 : b - 1 ∈ maximalIdeal C := by
    have e : b - 1 = -(b * (w 0 - 1)) := by linear_combination hb
    rw [e]
    exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (hwm 0))
  obtain ⟨t, ht⟩ : ∃ t : Fin 4 → C, t = ![1, 1, a, b] := ⟨_, rfl⟩
  have htw : ∀ i, t i.rev * w i * t i = 1 := by
    intro i
    fin_cases i <;> simp [ht, Fin.rev, h21, h30] <;>
      first | linear_combination ha | linear_combination hb
  have htm : ∀ i, t i - 1 ∈ maximalIdeal C := by
    intro i
    fin_cases i <;> simp [ht] <;> first | exact ha1 | exact hb1
  refine ⟨u * Matrix.diagonal t, ?_, ?_, ?_, ?_⟩
  · show adj (u * Matrix.diagonal t) * (u * Matrix.diagonal t) = (1 : C) • (1 : M4 C)
    rw [adj_mul', adj_diag', one_smul]
    calc Matrix.diagonal (fun i => t i.rev) * adj u * (u * Matrix.diagonal t)
        = Matrix.diagonal (fun i => t i.rev) * (adj u * u) * Matrix.diagonal t := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hWd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
            ← Matrix.diagonal_one]
          congr 1
          funext i
          exact htw i
  · intro i j
    have e : u * Matrix.diagonal t - 1 = (u - 1) * Matrix.diagonal t + (Matrix.diagonal t - 1) := by
      noncomm_ring
    rw [e, Matrix.add_apply]
    refine Ideal.add_mem _ (mulL _ _ hu1 i j) ?_
    by_cases hij : i = j
    · subst hij
      rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact htm i
    · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero]
      exact Submodule.zero_mem _
  · have e : adj (u * Matrix.diagonal t) * g * (u * Matrix.diagonal t)
        = Matrix.diagonal (fun i => t i.rev) * (adj u * u) * Matrix.diagonal d * Matrix.diagonal t := by
      rw [adj_mul', adj_diag']
      calc Matrix.diagonal (fun i => t i.rev) * adj u * g * (u * Matrix.diagonal t)
          = Matrix.diagonal (fun i => t i.rev) * adj u * (g * u) * Matrix.diagonal t := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hgu]
            simp only [Matrix.mul_assoc]
    rw [e, hWd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    exact Matrix.isDiag_diagonal _
  · intro hB
    have hB' : ∀ i j, lamW i ≠ lamW j → g i j = 0 := hB
    obtain ⟨S, hS⟩ : ∃ S : M4 C, S = Matrix.diagonal (sg C) := ⟨_, rfl⟩
    have hSS : S * S = 1 := by
      rw [hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact sg_sq (R := C) i
    have hgS : g * S = S * g := by
      ext i j
      rw [hS, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases h : lamW i = lamW j
      · rw [sg_eq (R := C) i j h, mul_comm]
      · rw [hB' i j h]
        ring
    have hdS : Matrix.diagonal d * S = S * Matrix.diagonal d := by
      rw [hS, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    have h1 : ∀ i j, (S * u * S - 1) i j ∈ maximalIdeal C := by
      have e : S * u * S - 1 = S * (u - 1) * S := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS]
      intro i j
      rw [e]
      exact mulL _ _ (mulR _ _ hu1) i j
    have h2 : g * (S * u * S) = S * u * S * Matrix.diagonal d := by
      calc g * (S * u * S) = S * (g * u) * S := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgS, Matrix.mul_assoc S g u]
        _ = S * u * (Matrix.diagonal d * S) := by
            rw [hgu]
            simp only [Matrix.mul_assoc]
        _ = S * u * S * Matrix.diagonal d := by
            rw [hdS]
            simp only [Matrix.mul_assoc]
    obtain ⟨-, t', ht'⟩ := huniq (S * u * S) d h1 h2
    have hent2 : ∀ i j, sg C i * u i j * sg C j = u i j * t' j := by
      intro i j
      have := congrFun (congrFun ht' i) j
      simp only [hS, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
      exact this
    have ht'1 : ∀ j, t' j = 1 := by
      intro j
      have h := hent2 j j
      have hu : IsUnit (u j j) := unit_of_sub isUnit_one (by
        have := hu1 j j
        rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this)
      have h0 : u j j * (t' j - 1) = 0 := by
        linear_combination (-1 : C) * h + u j j * sg_sq (R := C) j
      exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h0)
    have hBu : ∀ i j, lamW i ≠ lamW j → u i j = 0 := by
      intro i j hij
      have h := hent2 i j
      rw [ht'1 j, mul_one] at h
      have h' : (2 : C) * u i j = 0 := by
        linear_combination (-1 : C) * h + u i j * sg_ne (R := C) i j hij
      exact h2u.mul_right_eq_zero.mp h'
    intro i j hij
    rw [Matrix.mul_diagonal, hBu i j hij, zero_mul]

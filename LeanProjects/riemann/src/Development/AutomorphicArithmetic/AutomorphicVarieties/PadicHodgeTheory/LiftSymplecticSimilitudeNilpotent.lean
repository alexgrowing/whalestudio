import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
open UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem adj_mul' (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem adj_adj' (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem adj_one' : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

private theorem adj_add' (X Y : M4 R) : adj (X + Y) = adj X + adj Y := by
  ext i j
  simp only [adj_apply, Matrix.add_apply, smul_add]

private theorem adj_sub' (X Y : M4 R) : adj (X - Y) = adj X - adj Y := by
  ext i j
  simp only [adj_apply, Matrix.sub_apply, smul_sub]

private theorem adj_smul' (c : R) (X : M4 R) : adj (c • X) = c • adj X := by
  ext i j
  simp only [adj_apply, Matrix.smul_apply]
  rw [smul_comm]

private theorem adj_map' (f : R →+* R') (X : M4 R) : f.mapMatrix (adj X) = adj (f.mapMatrix X) := by
  ext i j
  simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul]

private theorem isUnit_of_res {E B : Type} [Field E] [CommRing B] [Algebra E B] (π : B →ₐ[E] E)
    (hπ : ∀ a, π a = 0 → IsNilpotent a) (M : M4 B) (h : IsUnit ((π : B →+* E).mapMatrix M)) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
  rw [← RingHom.map_det] at h
  have h1 : IsUnit (algebraMap E B (π M.det)) := IsUnit.map (algebraMap E B) h
  have h2 : IsNilpotent (M.det - algebraMap E B (π M.det)) := hπ _ (by simp)
  have := h2.isUnit_add_left_of_commute h1 (Commute.all _ _)
  simpa using this

end SlopeTestRemainingChoices

theorem UpperTheory.lift_symplectic_similitude_nilpotent :
    ∀ {E B B' : Type} [Field E] [CharZero E] [CommRing B] [CommRing B'] [Algebra E B] [Algebra E B'] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ h' : (M4 B')ˣ, IsGSp 1 (h' : M4 B') → (h' : M4 B').map π' = 1 → ∃ h : (M4 B)ˣ, IsGSp 1 (h : M4 B) ∧ (h : M4 B).map π = 1 ∧ (h : M4 B).map p = (h' : M4 B') := by
  intro E B B' _ _ _ _ _ _ π hπ π' hπ' p hp hc h' hG hr
  generalize (h' : M4 B') = g at hG hr ⊢
  have hG' : adj g * g = 1 := by simpa [IsGSp] using hG
  have hr' : (π' : B' →+* E).mapMatrix g = 1 := hr
  have hcomp : ∀ X : M4 B, (π : B →+* E).mapMatrix X =
      (π' : B' →+* E).mapMatrix ((p : B →+* B').mapMatrix X) := by
    intro X
    ext i j
    subst hc
    rfl
  have hu0 : IsUnit ((π' : B' →+* E).mapMatrix (1 + g)) := by
    rw [map_add, map_one, hr']
    have := (IsUnit.mk0 (2 : E) two_ne_zero).map (algebraMap E (M4 E))
    rwa [map_ofNat, ← one_add_one_eq_two] at this
  obtain ⟨U, hU⟩ := isUnit_of_res π' hπ' _ hu0
  have hcm : Commute (U : M4 B') (g - 1) := by
    rw [hU]
    exact ((Commute.one_left _).add_left ((Commute.refl g).sub_right (Commute.one_right g)))
  have e1 : (U : M4 B') * ((↑U⁻¹ : M4 B') * (g - 1)) = g - 1 := Units.mul_inv_cancel_left _ _
  have e2 : ((↑U⁻¹ : M4 B') * (g - 1)) * U = g - 1 := by
    rw [mul_assoc, ← hcm.eq, Units.inv_mul_cancel_left]
  generalize (↑U⁻¹ : M4 B') * (g - 1) = Y' at e1 e2
  have hk : g * (1 - Y') = 1 + Y' := by
    have : g * (1 - Y') - (1 + Y') = -((1 + g) * Y' - (g - 1)) := by noncomm_ring
    rw [← sub_eq_zero, this, ← hU, e1, sub_self, neg_zero]
  have hY'0 : (π' : B' →+* E).mapMatrix Y' = 0 := by
    have := congrArg (π' : B' →+* E).mapMatrix e1
    rw [map_mul, map_sub, map_one, hr', sub_self, hU, hu0.mul_right_eq_zero] at this
    exact this
  have hadj : adj Y' = -Y' := by
    have hT : IsUnit (adj (U : M4 B')) :=
      ⟨⟨adj (U : M4 B'), adj (↑U⁻¹ : M4 B'), by rw [← adj_mul', Units.inv_mul, adj_one'],
        by rw [← adj_mul', Units.mul_inv, adj_one']⟩, rfl⟩
    rw [← add_eq_zero_iff_eq_neg, ← hT.mul_right_eq_zero, ← U.isUnit.mul_left_eq_zero]
    have : adj (U : M4 B') * (adj Y' + Y') * (U : M4 B') =
        adj (Y' * (U : M4 B')) * (U : M4 B') + adj (U : M4 B') * (Y' * (U : M4 B')) := by
      rw [adj_mul']; noncomm_ring
    rw [this, e2, hU, adj_sub', adj_add', adj_one']
    have e3 : (adj g - 1) * (1 + g) + (1 + adj g) * (g - 1) =
        (adj g * g - 1) + (adj g * g - 1) := by noncomm_ring
    rw [e3, hG', sub_self, add_zero]
  obtain ⟨Z, hZ⟩ : ∃ Z : M4 B, (p : B →+* B').mapMatrix Z = Y' :=
    ⟨Matrix.of fun i j => (hp (Y' i j)).choose, by
      ext i j
      exact (hp (Y' i j)).choose_spec⟩
  obtain ⟨Y, hY, hYa⟩ : ∃ Y : M4 B, (p : B →+* B').mapMatrix Y = Y' ∧ adj Y = -Y := by
    refine ⟨algebraMap E B 2⁻¹ • (Z - adj Z), ?_, ?_⟩
    · have h1 : (p : B →+* B').mapMatrix (Z - adj Z) = Y' + Y' := by
        rw [map_sub, adj_map', hZ, hadj, sub_neg_eq_add]
      ext i j
      have h2 : p ((Z - adj Z) i j) = Y' i j + Y' i j := congrFun (congrFun h1 i) j
      have h3 : algebraMap E B' 2⁻¹ * 2 = 1 := by
        rw [← map_ofNat (algebraMap E B') 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
      show p (algebraMap E B 2⁻¹ * (Z - adj Z) i j) = Y' i j
      rw [map_mul, h2, AlgHom.commutes, ← two_mul, ← mul_assoc, h3, one_mul]
    · rw [adj_smul', adj_sub', adj_adj', ← smul_neg, neg_sub]
  have hY0 : (π : B →+* E).mapMatrix Y = 0 := by rw [hcomp, hY, hY'0]
  obtain ⟨V, hV⟩ := isUnit_of_res π hπ (1 - Y) (by rw [map_sub, map_one, hY0, sub_zero]; exact isUnit_one)
  obtain ⟨V', hV'⟩ := isUnit_of_res π hπ (1 + Y) (by rw [map_add, map_one, hY0, add_zero]; exact isUnit_one)
  have e4 : ((V' * V⁻¹ : (M4 B)ˣ) : M4 B) * (1 - Y) = 1 + Y := by
    rw [← hV, ← hV', Units.val_mul, Units.inv_mul_cancel_right]
  refine ⟨V' * V⁻¹, ?_⟩
  generalize ((V' * V⁻¹ : (M4 B)ˣ) : M4 B) = h at e4 ⊢
  have hph : (p : B →+* B').mapMatrix h = g := by
    have h1 := congrArg (p : B →+* B').mapMatrix e4
    rw [map_mul, map_sub, map_add, map_one, hY, ← hk] at h1
    have h2 : IsUnit (1 - Y') := by
      have := V.isUnit.map (p : B →+* B').mapMatrix
      rwa [hV, map_sub, map_one, hY] at this
    exact h2.mul_left_inj.1 h1
  refine ⟨?_, ?_, hph⟩
  · have hT : IsUnit (1 + Y) := hV' ▸ V'.isUnit
    have hT' : IsUnit (1 - Y) := hV ▸ V.isUnit
    have a1 : adj (1 - Y) = 1 + Y := by rw [adj_sub', adj_one', hYa, sub_neg_eq_add]
    have a2 : adj (1 + Y) = 1 - Y := by rw [adj_add', adj_one', hYa, sub_eq_add_neg]
    unfold IsGSp
    rw [one_smul, ← sub_eq_zero, ← hT.mul_right_eq_zero, ← hT'.mul_left_eq_zero]
    have : (1 + Y) * (adj h * h - 1) * (1 - Y) =
        adj (h * (1 - Y)) * (h * (1 - Y)) - (1 + Y) * (1 - Y) := by
      rw [adj_mul', a1]
      simp only [mul_sub (1 + Y) (adj h * h), sub_mul _ _ (1 - Y), mul_one, mul_assoc]
    rw [this, e4, a2]
    noncomm_ring
  · show (π : B →+* E).mapMatrix h = 1
    rw [hcomp, hph, hr']

import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_sqz :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (μ : ResidueField O →+ C), IsSq O μ → ∃ e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C, (∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ) ∧ (∀ X Y, e (X + Y) = e X * e Y) ∧ (∀ X, (e X)⁻¹ = e (-X)) ∧ (∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)), A * X.map μ = (A.map (res O C) * X).map μ ∧ X.map μ * A = (X * A.map (res O C)).map μ) ∧ ∀ (x : GG n C) (X : Matrix (Fin n) (Fin n) (ResidueField O)), x * GG.ofGL (e X) = GG.ofGL (e ((GG.map (res O C : C →+* ResidueField O) x).adFun X)) * x := by
  intro O _ _ C _ _ _ n μ hμ
  have hsq : ∀ c d, μ c * μ d = 0 := by
    intro c d
    have h := hμ.mul (μ c) d
    rw [(res_eq_zero_iff O C _).2 (hμ.mem c), zero_mul, map_zero] at h
    exact h.symm
  have hL : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      A * X.map μ = (A.map (res O C) * X).map μ := by
    intro A X
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hμ.mul]
  have hR : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      X.map μ * A = (X * A.map (res O C)).map μ := by
    intro A X
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (X i k), hμ.mul, mul_comm]
  have hsqM : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), X.map μ * Y.map μ = 0 := by
    intro X Y
    ext i j
    simp [Matrix.mul_apply, hsq]
  have hadd : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), (X + Y).map μ = X.map μ + Y.map μ := by
    intro X Y
    ext i j
    simp
  have hzero : (0 : Matrix (Fin n) (Fin n) (ResidueField O)).map μ = 0 := by
    ext i j
    simp
  have hu : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O),
      (1 + X.map μ) * (1 + Y.map μ) = 1 + (X + Y).map μ := by
    intro X Y
    rw [hadd, show (1 + X.map μ) * (1 + Y.map μ) = 1 + (X.map μ + Y.map μ) + X.map μ * Y.map μ by
      noncomm_ring, hsqM, add_zero]
  let e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C := fun X =>
    ⟨1 + X.map μ, 1 + (-X).map μ, by rw [hu, add_neg_cancel, hzero, add_zero],
      by rw [hu, neg_add_cancel, hzero, add_zero]⟩
  have he : ∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ := fun X => rfl
  have hemul : ∀ X Y, e (X + Y) = e X * e Y := by
    intro X Y
    apply Units.ext
    rw [Units.val_mul, he, he, he, hu]
  have heinv : ∀ X, (e X)⁻¹ = e (-X) := fun X => Units.ext rfl
  have hconj : ∀ (g : GL (Fin n) C) (h : GL (Fin n) (ResidueField O))
      (Y : Matrix (Fin n) (Fin n) (ResidueField O)),
      (g : Matrix (Fin n) (Fin n) C).map (res O C) = (h : Matrix (Fin n) (Fin n) (ResidueField O)) →
      g * e Y = e ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y *
        (↑h⁻¹ : Matrix (Fin n) (Fin n) (ResidueField O))) * g := by
    intro g h Y hh
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he, he, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, hL, hR, hh, Matrix.mul_assoc ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y),
      Units.inv_mul, Matrix.mul_one]
  have hJ : (Jmat C n).map (res O C) = Jmat (ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have htheta : ∀ Y, theta (e Y) = e (thetaLie Y) := by
    intro Y
    apply Units.ext
    rw [theta_val, heinv, he, he, Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Jmat_mul_Jmat, ← Matrix.transpose_map, hL, hJ, hR, hJ]
    rw [show thetaLie Y = Jmat (ResidueField O) n * (-Y)ᵀ * Jmat (ResidueField O) n by
      simp [thetaLie, Matrix.transpose_neg]]
  refine ⟨e, he, hemul, heinv, fun A X => ⟨hL A X, hR A X⟩, ?_⟩
  intro x X
  obtain ⟨g, s⟩ := x
  have hh : (g : Matrix (Fin n) (Fin n) C).map (res O C) =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG n C)).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  have had : GG.adFun (GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG n C)) X =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG n C)).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) *
        (if s = 1 then X else thetaLie X) *
        (↑(GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG n C)).left⁻¹ :
          Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  rw [had]
  refine SemidirectProduct.ext ?_ ?_
  · simp only [GG.ofGL, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [sgnAct_one, if_pos rfl]
      exact hconj _ _ X hh
    · rw [sgnAct_neg_one, if_neg (by decide), htheta]
      exact hconj _ _ _ hh
  · simp only [GG.ofGL, SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one, one_mul]

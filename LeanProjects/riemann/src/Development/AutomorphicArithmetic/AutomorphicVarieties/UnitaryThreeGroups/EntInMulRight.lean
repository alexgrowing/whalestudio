import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

section SlopeTestRemainingChoices

variable {C : Type} [CommRing C] {m : ℕ} {I : Ideal C}

private theorem entIn_mul_left (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (A * X) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hX k b)

private theorem entIn_mul_right (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (X * A) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (hX a k)

private theorem entIn_thetaLie {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (thetaLie X) := by
  intro a b
  have h1 : EntIn I (Jmat C m * Xᵀ) := entIn_mul_left _ (fun a b => hX b a)
  have h2 : EntIn I (Jmat C m * Xᵀ * Jmat C m) := entIn_mul_right _ h1
  unfold thetaLie
  rw [Matrix.neg_apply]
  exact I.neg_mem (h2 a b)

private theorem entIn_mul_zero (hI : I * I = ⊥) {X Y : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) (hY : EntIn I Y) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hm : X a c * Y c b ∈ I * I := Ideal.mul_mem_mul (hX a c) (hY c b)
  rw [hI] at hm
  exact (Submodule.mem_bot C).1 hm

private def onePlus (X : Matrix (Fin m) (Fin m) C) (h : X * X = 0) : GL (Fin m) C where
  val := 1 + X
  inv := 1 - X
  val_inv := by simp [Matrix.add_mul, Matrix.mul_sub, h]
  inv_val := by simp [Matrix.mul_add, Matrix.sub_mul, h]

private theorem act_onePlus (s : ℤˣ) (X : Matrix (Fin m) (Fin m) C) (h : X * X = 0) :
    ((sgnAct m C s (onePlus X h) : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      1 + (if s = 1 then X else thetaLie X) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp [onePlus]
  · rw [sgnAct_neg_one, theta_val, if_neg (by decide)]
    show Jmat C m * (1 - X)ᵀ * Jmat C m = _
    rw [Matrix.transpose_sub, Matrix.transpose_one, mul_sub, sub_mul, mul_one, Jmat_mul_Jmat]
    unfold thetaLie
    rw [sub_eq_add_neg]

end SlopeTestRemainingChoices

theorem UpperTheory.V.U3.exists_isDeform :
    ∀ {G C : Type} [Group G] [CommRing C] {m : ℕ} (I : Ideal C) (r : G →* GG m C) (γ : G → Matrix (Fin m) (Fin m) C), I * I = ⊥ →
      (∀ g, EntIn I (γ g)) → IsCoc r γ → ∃ r' : G →* GG m C, IsDeform r γ r' := by
  intro G C _ _ m I r γ hI hγ hc
  have hsq : ∀ g, γ g * γ g = 0 := fun g => entIn_mul_zero hI (hγ g) (hγ g)
  let P : G → GG m C := fun g => SemidirectProduct.inl (onePlus (γ g) (hsq g)) * r g
  have hPr : ∀ g, (P g).right = (r g).right := fun g => by simp [P]
  have hPlG : ∀ g, (P g).left = onePlus (γ g) (hsq g) * (r g).left := fun g => by
    simp [P, SemidirectProduct.mul_left]
  have hPl : ∀ g, ((P g).left : Matrix (Fin m) (Fin m) C) = (1 + γ g) * (r g).mat := fun g => by
    rw [hPlG, Units.val_mul]
    rfl
  have h1 : γ 1 = 0 := by
    have := hc 1 1
    simpa using this
  refine ⟨{ toFun := P, map_one' := ?_, map_mul' := ?_ }, fun g => ⟨hPr g, hPl g⟩⟩
  · apply SemidirectProduct.ext
    · apply Units.ext
      rw [hPl, h1]
      simp [GG.mat]
    · rw [hPr]
      simp
  · intro g h
    show P (g * h) = P g * P h
    apply SemidirectProduct.ext
    · apply Units.ext
      have had : adRep r g (γ h) = (r g).mat * (if (r g).right = 1 then γ h else thetaLie (γ h)) * ((r g).left⁻¹ : GL (Fin m) C) := rfl
      have hE : EntIn I (if (r g).right = 1 then γ h else thetaLie (γ h)) := by
        split_ifs
        · exact hγ h
        · exact entIn_thetaLie (hγ h)
      have hE2 := entIn_mul_right (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) (entIn_mul_left (r g).mat hE)
      have hMiMg : (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) * (r g).mat = 1 := by
        simp [GG.mat]
      have hz : γ g * ((r g).mat * (if (r g).right = 1 then γ h else thetaLie (γ h))) = 0 := by
        have h0 := entIn_mul_zero hI (hγ g) hE2
        calc _ = γ g * ((r g).mat * (if (r g).right = 1 then γ h else thetaLie (γ h)) * ((r g).left⁻¹ : GL (Fin m) C)) * (r g).mat := by
              rw [mul_assoc (γ g), mul_assoc _ (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C), hMiMg, mul_one]
          _ = 0 := by rw [h0, zero_mul]
      rw [hPl, SemidirectProduct.mul_left, Units.val_mul, hPl, hPr, hPlG h, map_mul ((sgnAct m C) (r g).right), Units.val_mul, act_onePlus, hc, had, map_mul r]
      simp only [GG.mat, SemidirectProduct.mul_left, Units.val_mul]
      simp only [GG.mat] at hMiMg hz
      generalize (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = Mi at hMiMg hz ⊢
      generalize (if (r g).right = 1 then γ h else thetaLie (γ h)) = Z at hz ⊢
      generalize ((r g).left : Matrix (Fin m) (Fin m) C) = Mg at hMiMg hz ⊢
      generalize (((sgnAct m C (r g).right) (r h).left : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = N
      have e1 : Mg * Z * Mi * (Mg * N) = Mg * Z * N := by
        rw [mul_assoc (Mg * Z), ← mul_assoc Mi, hMiMg, one_mul]
      have e2 : γ g * Mg * (Z * N) = 0 := by
        rw [mul_assoc (γ g), ← mul_assoc Mg, ← mul_assoc (γ g), hz, zero_mul]
      rw [add_mul, add_mul, e1]
      simp only [one_mul, add_mul, mul_add, mul_one, mul_assoc] at e2 ⊢
      rw [e2, add_zero]
      abel
    · rw [hPr, SemidirectProduct.mul_right, hPr, hPr, map_mul, SemidirectProduct.mul_right]

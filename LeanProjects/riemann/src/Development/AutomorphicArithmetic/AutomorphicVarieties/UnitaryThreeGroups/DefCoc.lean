import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

section SlopeTestRemainingChoices

variable {C : Type} [CommRing C] {m : ℕ}

private theorem entIn_mul_left (I : Ideal C) (A X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) :
    EntIn I (A * X) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hX k b)

private theorem entIn_mul_right (I : Ideal C) (A X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) :
    EntIn I (X * A) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (hX a k)

private theorem mul_eq_zero_of_entIn (I : Ideal C) (hI : I * I = ⊥) (X Y : Matrix (Fin m) (Fin m) C)
    (hX : EntIn I X) (hY : EntIn I Y) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  have h := Ideal.mul_mem_mul (hX a k) (hY k b)
  rw [hI, Ideal.mem_bot] at h
  exact h

private theorem entIn_thetaLie (I : Ideal C) (X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) :
    EntIn I (thetaLie X) := by
  intro a b
  simp only [thetaLie, Matrix.neg_apply]
  exact I.neg_mem (entIn_mul_right I _ _ (entIn_mul_left I _ _ (fun i j => hX j i)) a b)

private theorem sgnAct_one_add (I : Ideal C) (hI : I * I = ⊥) (q : GL (Fin m) C)
    (X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) (hq : (q : Matrix (Fin m) (Fin m) C) = 1 + X)
    (s : ℤˣ) :
    ((sgnAct m C s q : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      1 + (if s = 1 then X else thetaLie X) := by
  have hXX : X * X = 0 := mul_eq_zero_of_entIn I hI X X hX hX
  by_cases hs : s = 1
  · subst hs
    rw [if_pos rfl, map_one, MulAut.one_apply, hq]
  · have hs' : s = -1 := by
      rcases Int.units_eq_one_or s with h | h
      · exact absurd h hs
      · exact h
    subst hs'
    rw [sgnAct_neg_one, theta_val, if_neg hs]
    have h1 : (q : Matrix (Fin m) (Fin m) C) * ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : (1 - X) * (q : Matrix (Fin m) (Fin m) C) = 1 := by
      rw [hq, sub_mul, one_mul, mul_add, mul_one, hXX, add_zero, add_sub_cancel_right]
    have hinv : ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 - X := by
      calc ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C)
          = ((1 - X) * (q : Matrix (Fin m) (Fin m) C)) * ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := by
            rw [h2, one_mul]
        _ = (1 - X) * ((q : Matrix (Fin m) (Fin m) C) * ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C)) := mul_assoc _ _ _
        _ = 1 - X := by rw [h1, mul_one]
    rw [hinv, Matrix.transpose_sub, Matrix.transpose_one, mul_sub, sub_mul, mul_one, Jmat_mul_Jmat, thetaLie,
      sub_eq_add_neg]

end SlopeTestRemainingChoices

theorem UpperTheory.V.U3.exists_isCoc :
    ∀ {G C : Type} [Group G] [CommRing C] {m : ℕ} (I : Ideal C) (r r' : G →* GG m C), I * I = ⊥ →
      (GG.map (Ideal.Quotient.mk I)).comp r' = (GG.map (Ideal.Quotient.mk I)).comp r →
      ∃ γ : G → Matrix (Fin m) (Fin m) C, (∀ g, EntIn I (γ g)) ∧ IsCoc r γ ∧ IsDeform r γ r' := by
  intro G C _ _ m I r r' hI hr
  have hR : ∀ g, (r' g).right = (r g).right := by
    intro g
    have h := congrArg SemidirectProduct.right (DFunLike.congr_fun hr g)
    simpa [GG.map] using h
  have hM : ∀ g, ((r' g).left : Matrix (Fin m) (Fin m) C).map (Ideal.Quotient.mk I)
      = ((r g).left : Matrix (Fin m) (Fin m) C).map (Ideal.Quotient.mk I) := by
    intro g
    have h := congrArg GG.mat (DFunLike.congr_fun hr g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, GG.map_mat, GG.map_mat] at h
    exact h
  obtain ⟨q, hqdef⟩ : ∃ q : G → GL (Fin m) C, ∀ g, q g = (r' g).left * ((r g).left)⁻¹ := ⟨_, fun _ => rfl⟩
  have hE : ∀ g, EntIn I ((q g : Matrix (Fin m) (Fin m) C) - 1) := by
    intro g a b
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h1 : (Ideal.Quotient.mk I).mapMatrix ((q g : Matrix (Fin m) (Fin m) C) - 1) = 0 := by
      rw [map_sub, map_one, hqdef, Units.val_mul, map_mul, RingHom.mapMatrix_apply, hM g,
        ← RingHom.mapMatrix_apply, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, sub_self]
    have h2 := congrFun (congrFun h1 a) b
    simpa using h2
  refine ⟨fun g => (q g : Matrix (Fin m) (Fin m) C) - 1, hE, ?_, ?_⟩
  · intro g h
    have hq : q (g * h) = q g * ((r g).left * sgnAct m C (r g).right (q h) * ((r g).left)⁻¹) := by
      simp only [hqdef, map_mul, SemidirectProduct.mul_left, hR g, map_inv]
      group
    have had : ∀ Y, adRep r g Y = (((r g).left : Matrix (Fin m) (Fin m) C) * (if (r g).right = 1 then Y else thetaLie Y))
        * ((((r g).left)⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := fun Y => rfl
    have hφ := sgnAct_one_add I hI (q h) _ (hE h) (by abel) (r g).right
    have hAA : ((r g).left : Matrix (Fin m) (Fin m) C) * ((((r g).left)⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hYE : EntIn I (if (r g).right = 1 then (q h : Matrix (Fin m) (Fin m) C) - 1 else thetaLie ((q h : Matrix (Fin m) (Fin m) C) - 1)) := by
      split_ifs
      · exact hE h
      · exact entIn_thetaLie I _ (hE h)
    show (q (g * h) : Matrix (Fin m) (Fin m) C) - 1 = ((q g : Matrix (Fin m) (Fin m) C) - 1) + adRep r g ((q h : Matrix (Fin m) (Fin m) C) - 1)
    rw [had, hq]
    simp only [Units.val_mul]
    rw [hφ]
    generalize (if (r g).right = 1 then (q h : Matrix (Fin m) (Fin m) C) - 1 else thetaLie ((q h : Matrix (Fin m) (Fin m) C) - 1)) = Y at hYE ⊢
    generalize ((r g).left : Matrix (Fin m) (Fin m) C) = A at hAA ⊢
    generalize ((((r g).left)⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = B at hAA ⊢
    have e1 : A * (1 + Y) * B = 1 + A * Y * B := by
      rw [mul_add, mul_one, add_mul, hAA]
    rw [e1]
    have hAY : EntIn I (A * Y * B) := entIn_mul_right I B (A * Y) (entIn_mul_left I A Y hYE)
    have hN := mul_eq_zero_of_entIn I hI ((q g : Matrix (Fin m) (Fin m) C) - 1) (A * Y * B) (hE g) hAY
    generalize A * Y * B = M at hN ⊢
    generalize (q g : Matrix (Fin m) (Fin m) C) = Q at hN ⊢
    have e2 : Q * (1 + M) = Q + M + (Q - 1) * M := by noncomm_ring
    rw [e2, hN]
    abel
  · intro g
    refine ⟨hR g, ?_⟩
    simp only [GG.mat]
    rw [add_sub_cancel, hqdef, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

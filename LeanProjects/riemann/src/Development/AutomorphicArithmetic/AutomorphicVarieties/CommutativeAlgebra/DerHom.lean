import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.der_hom :
    ∀ (O A B Q : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B] [AddCommGroup Q] [Module O Q] [Module B Q] [Module Bᵐᵒᵖ Q] [IsCentralScalar B Q] [IsScalarTower O B Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] [IsScalarTower O Bᵐᵒᵖ Q] (x : A →ₐ[O] B) (D : A → Q),
      (∃ D' ∈ PtDer x Q, ⇑D' = D) ↔ ∃ y : A →ₐ[O] TrivSqZeroExt B Q, ∀ f, (y f).fst = x f ∧ (y f).snd = D f := by
  intro O A B Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ x D
  constructor
  · rintro ⟨D', hD', rfl⟩
    have hL : ∀ f g : A, D' (f * g) = x f • D' g + x g • D' f := hD'
    have h1 : D' 1 = 0 := by
      have h := hL 1 1
      simp only [mul_one, map_one, one_smul] at h
      exact left_eq_add.mp h
    refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (D' f)
              map_one' := ?_
              map_mul' := ?_
              map_zero' := ?_
              map_add' := ?_
              commutes' := ?_ }, fun f => ?_⟩
    · ext <;> simp [h1]
    · intro f g
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.fst_inr, add_zero, zero_add, op_smul_eq_smul, hL]
    · ext <;> simp
    · intro f g
      ext <;> simp [add_add_add_comm]
    · intro r
      rw [TrivSqZeroExt.algebraMap_eq_inl']
      have h0 : D' (algebraMap O A r) = 0 := by
        rw [Algebra.algebraMap_eq_smul_one, D'.map_smul, h1, smul_zero]
      ext <;> simp [h0]
    · simp
  · rintro ⟨y, hy⟩
    have hD : ∀ f, D f = (y f).snd := fun f => (hy f).2.symm
    have hX : ∀ f, x f = (y f).fst := fun f => (hy f).1.symm
    refine ⟨{ toFun := D
              map_add' := ?_
              map_smul' := ?_ }, ?_, rfl⟩
    · intro f g
      simp only [hD, map_add, TrivSqZeroExt.snd_add]
    · intro r f
      simp only [hD, map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]
    · show ∀ f g : A, _ = _
      intro f g
      show D (f * g) = x f • D g + x g • D f
      rw [hD, hD, hD, hX, hX, map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, add_comm]

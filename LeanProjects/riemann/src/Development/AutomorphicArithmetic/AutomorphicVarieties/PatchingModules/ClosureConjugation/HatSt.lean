import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.EpsEq

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.hat_st :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ y, H.r (H.T.st y) = (H.r y)ᵀ := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hf H
  have key : ∀ g : G.G₀, (algebraMap B Bh) ↑((G.frame.eps O B) g ^ (1 - (n : ℤ))) •
      ((mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹)).map (algebraMap x.A (FractionRing x.A)) =
      (((mat x.ρ) (h.p₀ g)).map (algebraMap x.A (FractionRing x.A)))ᵀ := by
    intro g
    obtain ⟨he, hc⟩ := eps_eq P g
    have hunit : P.f (↑((G.frame.eps O B) g ^ (1 - (n : ℤ))) : B) =
        ↑((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))) := by
      have hu : Units.map (P.f : B →* x.A) ((G.frame.eps O B) g) =
          (G0.frame.eps ℤ_[l] x.A) (h.p₀ g) := by
        apply Units.ext
        rw [Units.coe_map]
        exact he
      rw [← hu, ← map_zpow (Units.map (P.f : B →* x.A)), Units.coe_map]
      rfl
    have hinvM : (mat x.ρ) (h.p₀ (G.frame.conj g)) * (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    have hA : ((mat x.ρ) (h.p₀ g))ᵀ =
        (↑((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))) : x.A) •
          (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹) := by
      have hform := x.form (h.p₀ g)
      rw [Units.val_one, Matrix.mul_one, ← hc] at hform
      calc ((mat x.ρ) (h.p₀ g))ᵀ = ((mat x.ρ) (h.p₀ g))ᵀ * ((mat x.ρ) (h.p₀ (G.frame.conj g)) *
            (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹)) := by rw [hinvM, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hform, Matrix.smul_mul, Matrix.one_mul]
    rw [← Matrix.transpose_map, hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [Algebra.smul_def, hf, hunit]
  intro y
  obtain ⟨z, rfl⟩ := H.surj y
  refine MonoidAlgebra.induction_on (motive := fun z => H.r (H.T.st (H.ι z)) = (H.r (H.ι z))ᵀ)
    z ?_ ?_ ?_
  · intro g
    rw [MonoidAlgebra.of_apply, H.st, map_smul, H.r_ι, H.r_ι]
    exact key g
  · intro a b ha hb
    simp only [map_add, ha, hb, Matrix.transpose_add]
  · intro c a ha
    simp only [map_smul, ha, Matrix.transpose_smul]

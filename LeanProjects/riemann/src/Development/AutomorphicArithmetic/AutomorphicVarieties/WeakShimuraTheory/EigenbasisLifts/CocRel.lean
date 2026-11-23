import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem cr_fst_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.fst = M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.fst :=
  Matrix.map_mul (f := dF K)

private theorem cr_snd_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.snd + M.map TrivSqZeroExt.snd * N.map TrivSqZeroExt.fst := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [smul_eq_mul, mul_comm]

private theorem cr_alg {K : Type} [CommRing K] {n : ℕ} (A B P Q y y' Ai Bi Pi : Matrix (Fin n) (Fin n) K) (e : K)
    (hA : Ai * A = 1) (hB : B * Bi = 1) (hP : Pi * P = 1) (hP' : P * Pi = 1)
    (h1 : Aᵀ * P * B = e • P)
    (h2 : Aᵀ * P * (y' * B) + (Aᵀ * Q + (y * A)ᵀ * P) * B = e • Q) :
    y' = -(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q) := by
  have hBi : Bi * B = 1 := mul_eq_one_comm.mp hB
  have hAi : A * Ai = 1 := mul_eq_one_comm.mp hA
  have canc : ∀ X : Matrix (Fin n) (Fin n) K, Pi * Aiᵀ * (Aᵀ * P * X * B) * Bi = X := by
    intro X
    simp only [Matrix.mul_assoc]
    rw [hB, Matrix.mul_one, ← Matrix.mul_assoc Aiᵀ Aᵀ, ← Matrix.transpose_mul, hAi, Matrix.transpose_one,
      Matrix.one_mul, ← Matrix.mul_assoc Pi P, hP, Matrix.one_mul]
  have lhs : Aᵀ * P * y' * B = e • Q - Aᵀ * (Q * B) - Aᵀ * (yᵀ * (P * B)) := by
    rw [Matrix.transpose_mul] at h2
    rw [← h2]
    simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
    abel
  have rhs : Aᵀ * P * (-(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q)) * B
      = e • Q - Aᵀ * (Q * B) - Aᵀ * (yᵀ * (P * B)) := by
    have t1 : Aᵀ * P * (Pi * yᵀ * P) * B = Aᵀ * (yᵀ * (P * B)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pi, hP', Matrix.one_mul]
    have t2 : Aᵀ * P * (B * (Pi * Q) * Bi) * B = e • Q := by
      calc Aᵀ * P * (B * (Pi * Q) * Bi) * B = (Aᵀ * P * B) * (Pi * Q) * (Bi * B) := by
            simp only [Matrix.mul_assoc]
        _ = e • Q := by
            rw [h1, hBi, Matrix.mul_one, Matrix.smul_mul, ← Matrix.mul_assoc, hP', Matrix.one_mul]
    have t3 : Aᵀ * P * (Pi * Q) * B = Aᵀ * (Q * B) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pi, hP', Matrix.one_mul]
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul, t1, t2, t3]
    abel
  rw [← canc y', ← canc (-(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q)), lhs, rhs]

theorem UpperTheory.V.Ws.Eb.cocRel :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] {K : Type} [Field K] [Algebra O K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (y : F.G₀ → Matrix (Fin n) (Fin n) K) (ρ' : F.G₀ →* GL (Fin n) (DualNumber K)) (P' : GL (Fin n) (DualNumber K)), IsTan ρ y ρ' → F.IsForm O n ρ' P' →
        F.IsForm O n ρ (Matrix.GeneralLinearGroup.map (dF K) P') ∧ ∀ R, IsAdExt F ρ (Matrix.GeneralLinearGroup.map (dF K) P') R → ∃ Z, ∀ g, y (F.conj g) = R F.c (y g) + (R (F.conj g) Z - Z) := by
  intro l _ F O _ _ K _ _ n ρ y ρ' P' hT hF
  have hfst : ∀ g, (W.mat ρ' g).map TrivSqZeroExt.fst = W.mat ρ g := by
    intro g; ext i j
    simp only [Matrix.map_apply]
    rw [show (W.mat ρ' g) i j = ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j) from rfl, hT g i j]
    rfl
  have hsnd : ∀ g, (W.mat ρ' g).map TrivSqZeroExt.snd = y g * W.mat ρ g := by
    intro g; ext i j
    simp only [Matrix.map_apply]
    rw [show (W.mat ρ' g) i j = ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j) from rfl, hT g i j]
    rfl
  have hP : (↑P' : Matrix (Fin n) (Fin n) (DualNumber K)).map TrivSqZeroExt.fst
      = (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hc : ∀ g, ((F.eps O (DualNumber K) g ^ (1 - (n : ℤ)) : (DualNumber K)ˣ) : DualNumber K)
      = (TrivSqZeroExt.inl ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) : DualNumber K) := by
    intro g
    have : F.eps O (DualNumber K) g = Units.map (TrivSqZeroExt.inlHom K K : K →* DualNumber K) (F.eps O K g) :=
      Units.ext rfl
    rw [this, ← map_zpow]; rfl
  have hs1 : ∀ (e : K) (M : Matrix (Fin n) (Fin n) (DualNumber K)),
      ((TrivSqZeroExt.inl e : DualNumber K) • M).map TrivSqZeroExt.fst = e • M.map TrivSqZeroExt.fst := by
    intro e M; ext i j; simp
  have hs2 : ∀ (e : K) (M : Matrix (Fin n) (Fin n) (DualNumber K)),
      ((TrivSqZeroExt.inl e : DualNumber K) • M).map TrivSqZeroExt.snd = e • M.map TrivSqZeroExt.snd := by
    intro e M; ext i j; simp
  have part1 : ∀ g, (W.mat ρ g)ᵀ * (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K)
      * W.mat ρ (F.conj g)
      = ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) •
        (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K) := by
    intro g
    have h := congrArg (fun M => M.map TrivSqZeroExt.fst) (hF g)
    rw [cr_fst_mul, cr_fst_mul] at h
    simp only [Matrix.transpose_map, hfst, hP, hc, hs1] at h
    exact h
  refine ⟨fun g => part1 g, fun R hR => ?_⟩
  refine ⟨(↑(Matrix.GeneralLinearGroup.map (dF K) P')⁻¹ : Matrix (Fin n) (Fin n) K) *
    (↑P' : Matrix (Fin n) (Fin n) (DualNumber K)).map TrivSqZeroExt.snd, fun g => ?_⟩
  have h := congrArg (fun M => M.map TrivSqZeroExt.snd) (hF g)
  rw [cr_snd_mul, cr_fst_mul, cr_snd_mul] at h
  simp only [Matrix.transpose_map, hfst, hsnd, hP, hc, hs2] at h
  rw [hR.c, hR.ad]
  exact cr_alg (A := W.mat ρ g) (B := W.mat ρ (F.conj g)) (Ai := ↑(ρ g)⁻¹) (Bi := ↑(ρ (F.conj g))⁻¹)
    (Pi := ↑(Matrix.GeneralLinearGroup.map (dF K) P')⁻¹) (hA := Units.inv_mul _) (hB := Units.mul_inv _)
    (hP := Units.inv_mul _) (hP' := Units.mul_inv _) (h1 := part1 g) (h2 := h)

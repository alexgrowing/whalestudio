import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

private theorem theta_theta {K : Type} [Field K] (Δ : K) (x : U3 Δ) : theta Δ (theta Δ x) = x := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  exact star_star ((x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)

private theorem mul_theta_conj {K : Type} [Field K] (Δ : K) (δ x : U3 Δ) :
    (x⁻¹ * δ * theta Δ x) * theta Δ (x⁻¹ * δ * theta Δ x) = x⁻¹ * (δ * theta Δ δ) * x := by
  simp only [map_mul, map_inv, theta_theta, mul_assoc, mul_inv_cancel_left]

private theorem charpoly_conj {K : Type} [Field K] (Δ : K) (n x : U3 Δ) :
    ((x⁻¹ * n * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).charpoly =
      (n : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).charpoly := by
  have e : ((x⁻¹ * n * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
      ((x⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((n * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) := by
    rw [mul_assoc]; rfl
  rw [e, Matrix.charpoly_mul_comm]
  have e2 : ((n * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((x⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) =
      ((n * x * x⁻¹ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) := rfl
  rw [e2, mul_inv_cancel_right]

private theorem lmap_star {K K' : Type} [Field K] [Field K'] (f : K →+* K') (Δ : K) (x : Lsq K Δ) :
    lmap f Δ (star x) = star (lmap f Δ x) := by
  ext <;> simp [lmap]

open Polynomial in
private theorem poly_expand {R : Type} [CommRing R] (t : R) :
    ((X - 1) * (X ^ 2 - C t * X + 1) : R[X]) = X ^ 3 - C (1 + t) * X ^ 2 + C (1 + t) * X - 1 := by
  simp only [C_add, C_1]; ring

open Polynomial in
theorem UpperTheory.V.Z.Sym.Glob.sideGTau :
    (∀ (K : Type) [Field K] (Δ : K) (δ x : U3 Δ) (τ : K), HasTau δ τ → HasTau (x⁻¹ * δ * theta Δ x) τ) ∧
    (∀ (K : Type) [Field K] (Δ : K) (δ : U3 Δ) (τ τ' : K), HasTau δ τ → HasTau δ τ' → τ = τ') ∧
    (∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (Δ : K) (δ : U3 Δ) (δ' : U3 (f Δ)) (τ : K),
      (δ' : Matrix (Fin 3) (Fin 3) _) = (δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (lmap f Δ) → HasTau δ τ → HasTau δ' (f τ)) ∧
    ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (Δ : K) (δ : U3 Δ) (τ : K), δ ∈ KU O Δ → HasTau δ τ → IsIntegral O τ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K _ Δ δ x τ h
    unfold HasTau at h ⊢
    rw [mul_theta_conj, charpoly_conj, h]
  · intro K _ Δ δ τ τ' h h'
    unfold HasTau at h h'
    have e := h.symm.trans h'
    have m : (X - 1 : (Lsq K Δ)[X]).Monic := by
      simpa using Polynomial.monic_X_sub_C (1 : Lsq K Δ)
    have e1 := m.isRegular.left e
    have e2 := congrArg (fun p => p.coeff 1) e1
    simp [coeff_X, coeff_one, coeff_X_pow] at e2
    exact e2
  · intro K K' _ _ f Δ δ δ' τ hd h
    unfold HasTau at h ⊢
    have e : ((δ' * theta (f Δ) δ' : U3 (f Δ)) : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) =
        ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (lmap f Δ) := by
      have a : ((theta (f Δ) δ' : U3 (f Δ)) : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) =
          ((theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map (lmap f Δ) := by
        refine Matrix.ext fun i j => ?_
        change star ((δ' : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) i j) = lmap f Δ (star ((δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))
        rw [hd, lmap_star]; rfl
      change (δ' : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) * ((theta (f Δ) δ' : U3 (f Δ)) : Matrix (Fin 3) (Fin 3) (Lsq K' (f Δ))) = _
      rw [a, hd]
      exact (Matrix.map_mul (f := lmap f Δ)).symm
    have hl : lmap f Δ (algebraMap K (Lsq K Δ) τ) = algebraMap K' (Lsq K' (f Δ)) (f τ) := by
      ext <;> simp [lmap]
    rw [e, Matrix.charpoly_map, h]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_one, hl]
  · intro O K _ _ _ Δ δ τ hK h
    unfold HasTau at h
    have hθ : theta Δ δ ∈ KU O Δ := fun i j => by
      refine ⟨(hK i j).2, ?_⟩
      change IsIntegral O (star (star ((δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)))
      rw [star_star]; exact (hK i j).1
    have hN := (KU O Δ).mul_mem hK hθ
    have ht : IsIntegral O (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ))).trace :=
      IsIntegral.sum _ fun i _ => (hN i i).1
    have hc := Matrix.trace_eq_neg_charpoly_coeff ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ))
    have c2 : ∀ s : Lsq K Δ, (X ^ 3 - C s * X ^ 2 + C s * X - 1 : (Lsq K Δ)[X]).coeff (Fintype.card (Fin 3) - 1) = -s := by
      intro s
      simp [coeff_X, coeff_one, coeff_X_pow, coeff_C_mul]
    rw [h, poly_expand, c2, neg_neg] at hc
    rw [hc] at ht
    have h2 : IsIntegral O (algebraMap K (Lsq K Δ) τ) := by
      simpa using ht.sub isIntegral_one
    refine (isIntegral_algebraMap_iff ?_).1 h2
    intro a b hab
    simpa using congrArg QuadraticAlgebra.re hab

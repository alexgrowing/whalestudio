import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def UpperTheory.V.Ws.pairJ (k : Type) [Field k] : M4 k := !![0,0,0,1; 0,0,1,0; 0,-1,0,0; -1,0,0,0]

private theorem UpperTheory.V.Ws.pairJ_sq (k : Type) [Field k] : pairJ k * pairJ k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairJ, Matrix.mul_apply, Fin.sum_univ_four]

private theorem UpperTheory.V.Ws.pairJ_adj {k : Type} [Field k] (X : M4 k) :
    X.transpose * pairJ k = pairJ k * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairJ, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]

theorem UpperTheory.V.Ws.auPair :
    ∀ {k Γ : Type} [Field k] [Group Γ] (r : Γ →* M4 k) (μ : Γ →* kˣ), (∀ g, IsGSp (μ g : k) (r g)) → ∀ c : Γ, ∃ P : GL (Fin 4) k, ∀ s : Γ, (r s).transpose * (P : M4 k) * r (c * s * c⁻¹) = (μ s : k) • (P : M4 k) := by
  intro k Γ _ _ r μ h c
  refine ⟨⟨pairJ k * r c⁻¹, -(r c * pairJ k), ?_, ?_⟩, fun s => ?_⟩
  · rw [mul_neg, mul_assoc, ← mul_assoc (r c⁻¹), ← map_mul, inv_mul_cancel, map_one, one_mul, pairJ_sq, neg_neg]
  · rw [neg_mul, mul_assoc, ← mul_assoc (pairJ k), pairJ_sq, neg_mul, one_mul, mul_neg, neg_neg, ← map_mul,
      mul_inv_cancel, map_one]
  · show (r s).transpose * (pairJ k * r c⁻¹) * r (c * s * c⁻¹) = (μ s : k) • (pairJ k * r c⁻¹)
    have e : r c⁻¹ * r (c * s * c⁻¹) = r s * r c⁻¹ := by
      rw [← map_mul, ← map_mul]; congr 1; group
    have hs : adj (r s) * r s = (μ s : k) • (1 : M4 k) := h s
    rw [mul_assoc, mul_assoc, e, ← mul_assoc, pairJ_adj, mul_assoc, ← mul_assoc (adj _), hs,
      smul_mul_assoc, one_mul, mul_smul_comm]

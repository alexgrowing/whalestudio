import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  intro l _ Ω _ _ _ e S A W hW c hc s i j

  have hdet : (mat W s).det ∈ c.O := by
    let M : Matrix (Fin 2) (Fin 2) c.O := Matrix.of fun i j => ⟨mat W s i j, hc s i j⟩
    have hM : M.map c.O.val = mat W s := by ext i j; rfl
    have h := RingHom.map_det (SubringClass.subtype c.O) M
    rw [RingHom.mapMatrix_apply] at h
    rw [← hM]
    have e1 : (M.map c.O.val) = M.map (SubringClass.subtype c.O) := rfl
    rw [e1, ← h]
    exact (M.det).2

  have hinv : (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
    have h2 : dt W s ^ 2 = 1 := by
      have := congrArg (fun f => f s) hW.det2
      simpa using this
    have : (dt W s)⁻¹ = dt W s := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, h2]
    rw [this]; rfl
  have hcyc : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) ∈ c.O := by
    show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O
    exact c.O.algebraMap_mem _
  have hval : mat (dual1 W) s i j = ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) * (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) * mat W s i j := by
    simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, MonoidHom.inv_apply]
  rw [hval, hinv]
  exact c.O.mul_mem (c.O.mul_mem hcyc hdet) (hc s i j)

end GlobalTheory.Ord2

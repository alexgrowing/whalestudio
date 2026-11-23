import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzany
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ChiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.psiReal :
    PsiBound → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω] [IsScalarTower ℚ E Ω] [IsAlgClosure E Ω] [IsAlgClosure ℚ Ω] [IsAbelianGalois ℚ E] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ Module.finrank ℚ E → ∀ (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] (e : ℕ), 1 ≤ e → ∀ ψ : (E ≃ₐ[ℚ] E) →* Oˣ, chiOf ρ ψ (-1) = (-1) ^ (e + 1) → psiLen (l := l) Ω e ψ ≠ ⊤ ∧ ((psiLen (l := l) Ω e ψ).toNat : ℝ) * Real.log l ≤ ((eO l O).toNat : ℝ) * -Real.log ‖alN (e + 1) (chiOf ρ ψ)‖ := by
  intro hPB E Ω _ _ _ _ _ _ _ _ _ _ N _ ρ hρ l _ hl2 hlE O _ _ e he ψ hψ
  obtain ⟨hsurj, -⟩ := actFacts E Ω N ρ hρ
  obtain ⟨-, hF⟩ := chiFacts E N ρ hsurj l O
  obtain ⟨-, a, ha⟩ := hF ψ (e + 1)
  have hle := hPB E Ω N ρ hρ l hl2 hlE O e he ψ hψ a ha
  have hB := (b_nzany (chiOf ρ ψ) (e + 1) (by omega) hψ).1
  have hane : (a : PadicAlgCl l) ≠ 0 := by
    rw [ha]
    simp only [alN]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (den_pos (Nat.pos_of_ne_zero (NeZero.ne N)) _).ne') hB
  have ha0 : a ≠ 0 := fun h => hane (by simp [h])
  have hval : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using ha0
  refine ⟨ne_top_of_le_ne_top hval hle, ?_⟩
  have hn := normO l O a ha0
  have hpos : 0 < ‖(a : PadicAlgCl l)‖ := norm_pos_iff.mpr hane
  have hlog := congrArg Real.log hn
  rw [Real.log_pow, Real.log_pow, Real.log_inv] at hlog
  rw [← ha]
  have hmono : ((psiLen (l := l) Ω e ψ).toNat : ℝ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℝ) := by
    exact_mod_cast ENat.toNat_le_toNat hle hval
  have hl : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
  nlinarith [mul_le_mul_of_nonneg_right hmono hl]

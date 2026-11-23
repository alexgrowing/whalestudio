import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem ps_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (i : Fin 4) (g : G ℚ Ω) : D.ps i g = D.al g ^ lamW i * D.Psi g ^ muW i := by
  fin_cases i <;> simp [Raw.ps, Raw.th, lamW, muW]

private theorem rbar_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (g : G ℚ Ω) : D.rbar g = Matrix.diagonal fun i => residue c.O (D.ps i g : c.O) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Raw.rbar, Raw.r0, mapRep, diagRep]
  · simp [Raw.rbar, Raw.r0, mapRep, diagRep, Matrix.diagonal_apply, h]

theorem UpperTheory.V.X.spAct :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (rb : D.Gam →* M4 (ResidueField c.O)), rb.comp (toGS Ω D.SP) = D.rbar → ∀ (h : (form c.O).Normalises rb) (j : ℤ × ℤ) (g : G ℚ Ω) (Y : (form c.O).gw (ResidueField c.O) j), Alg.FormData.adRep h j (toGS Ω D.SP g) Y = Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) g • Y := by
  intro Ω _ _ _ l _ c D rb hrb h j g Y
  apply Subtype.ext
  show rb (toGS Ω D.SP g) * (Y : Matrix (Fin 4) (Fin 4) (ResidueField c.O)) * rb (toGS Ω D.SP g)⁻¹ = _
  rw [← map_inv, ← MonoidHom.comp_apply rb, ← MonoidHom.comp_apply rb, hrb, rbar_eq, rbar_eq]
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Submodule.coe_smul, Matrix.smul_apply, smul_eq_mul]
  by_cases hab : w4 a - w4 b = j
  · have key : D.ps a g * D.ps b g⁻¹ = (D.al ^ j.1 * D.Psi ^ j.2) g := by
      subst hab
      rw [map_inv, ps_eq, ps_eq, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.zpow_apply]
      simp only [w4, Prod.fst_sub, Prod.snd_sub, zpow_sub, div_eq_mul_inv, mul_inv]
      ac_rfl
    rw [Raw.bar, ← key, Units.val_mul, map_mul]
    ring
  · have hz : (Y : Matrix (Fin 4) (Fin 4) (ResidueField c.O)) a b = 0 := (Submodule.mem_inf.1 Y.2).2 a b hab
    simp [hz]

import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem UpperTheory.V.Kum.restriction_infinity_sign_eigen
    (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (D : LData F Ω l) (e : ℕ) (σ : Ω ≃+* Ω) (h : IsConjOm σ) (s : ℤ_[l]) (hss : s * s = 1) (x : H1 (qzTw D (e : ℤ)))
    (hx : x ∈ Sha D (e : ℤ)) (hx' : x ∈ (cAct D e).eigenspace ((-1) ^ e * s)) :
    resInf D e x ∈ EqEig l (Uinf F Ω l) (qzG F Ω l e) σ s := by
  refine ⟨UpperTheory.V.Kum.resInfMem F Ω l D e ⟨x, hx, rfl⟩, fun u u' huu => ?_⟩
  have h1 := UpperTheory.V.Kum.resInfConj F Ω l D e (cE F) σ h.isLift x u u' huu
  rw [Module.End.mem_eigenspace_iff, cAct] at hx'
  rw [hx', twScal_conj (E := F) h, map_smul, Pi.smul_apply] at h1
  have hs : (-1 : ℤ_[l]) ^ e * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  have h2 := congrArg (fun m => (s * (-1 : ℤ_[l]) ^ e) • m) h1
  have k1 : s * (-1 : ℤ_[l]) ^ e * ((-1) ^ e * s) = 1 := by
    rw [mul_assoc, ← mul_assoc ((-1 : ℤ_[l]) ^ e), hs, one_mul, hss]
  have k2 : s * (-1 : ℤ_[l]) ^ e * (-1) ^ e = s := by rw [mul_assoc, hs, mul_one]
  simp only [smul_smul, k1, k2, one_smul] at h2
  exact h2

theorem UpperTheory.V.Kum.resInfSign :
    ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℕ) (σ : Ω ≃+* Ω), IsConjOm σ →
    (ShaPlus D e).map (resInf D e) ≤ EqEig l (Uinf F Ω l) (qzG F Ω l e) σ 1 ∧ (ShaMinus D e).map (resInf D e) ≤ EqEig l (Uinf F Ω l) (qzG F Ω l e) σ (-1) := by
  intro F Ω _ _ _ _ _ _ l _ D e σ h
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact UpperTheory.V.Kum.restriction_infinity_sign_eigen F Ω l D e σ h 1 (mul_one _) x hx.1 (by rw [mul_one]; exact hx.2)
  · rintro _ ⟨x, hx, rfl⟩
    exact UpperTheory.V.Kum.restriction_infinity_sign_eigen F Ω l D e σ h (-1) (by simp) x hx.1 (by rw [← pow_succ]; exact hx.2)

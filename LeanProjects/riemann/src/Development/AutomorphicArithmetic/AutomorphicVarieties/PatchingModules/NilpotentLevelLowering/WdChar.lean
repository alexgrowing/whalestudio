import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem unip_eq_one {n d : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hd : d ≠ 0) (h1 : M ^ d = 1)
    (hc : M.charpoly = (Polynomial.X - 1) ^ n) : M = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hsep : (Polynomial.X ^ d - Polynomial.C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hd) one_ne_zero
  have h1' : minpoly ℂ M ∣ Polynomial.X ^ d - Polynomial.C 1 := minpoly.dvd ℂ M (by simp [h1])
  have hsq : Squarefree (minpoly ℂ M) := hsep.squarefree.squarefree_of_dvd h1'
  have h2 : minpoly ℂ M ∣ (Polynomial.X - 1) ^ n := hc ▸ Matrix.minpoly_dvd_charpoly M
  have h3 : minpoly ℂ M ∣ Polynomial.X - 1 := (hsq.dvd_pow_iff_dvd hn.ne').mp h2
  have h4 := (minpoly.dvd_iff).mp h3
  simpa [sub_eq_zero] using h4

theorem UpperTheory.V.Pa.Lev.wdChar :
    ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (x : WD hB), IsWDOf ι r x → (∀ σ : Weil hB, ((r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι).charpoly = x.charPol σ) ∧ ∀ σ ∈ GlobalTheory.TameQuot.ineKer E Bq l, ((r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι).charpoly = (Polynomial.X - 1) ^ n → r σ = 1 := by
  intro l _ E Ω _ _ _ _ _ Bq w hB hl n ι r x hx
  have hxe : wdOf hB hl ι r = x := IsWDOf.wdOf_eq hl hx
  obtain ⟨t, ht, φ, hφ, N, a, hmon, -, -⟩ := hx
  constructor
  · intro σ
    rw [← hxe, IsMonodromy.charPol_wdOf hl ht hmon ι σ]
    exact Matrix.charpoly_map _ ι.toRingHom
  · intro σ hσ hc
    have hσI : σ ∈ Ine Bq := GlobalTheory.TameQuot.ineKer_le_Ine Bq l hσ
    let τ : Ine Bq := ⟨σ, hσI⟩
    have htτ : t τ = 1 := (GlobalTheory.TameQuot.eq_one_iff_mem_ineKer E Ω l Bq w hB hl t ht.1 ht.2 τ).mpr hσ
    have hval : tval t τ = 0 := by simp [tval, htτ]
    obtain ⟨-, U, hU, hUr⟩ := hmon
    haveI := compactSpace_Ine (E := E) Bq
    haveI : Finite (Ine Bq ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
    haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hd : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hpow : τ ^ U.normalCore.index ∈ U := U.normalCore_le (U.normalCore.pow_index_mem τ)
    have hr : (r σ : Matrix (Fin n) (Fin n) (Qbar l)) ^ U.normalCore.index = 1 := by
      have := hUr _ hpow
      rw [tval_pow, hval, mul_zero, zero_smul, IsNilpotent.exp_zero, Subgroup.coe_pow, map_pow,
        Units.val_pow_eq_pow_val] at this
      exact this
    have hM : (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = 1 := by
      apply unip_eq_one _ hd _ hc
      have e : (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = ι.toRingHom.mapMatrix (r σ : Matrix (Fin n) (Fin n) (Qbar l)) := rfl
      rw [e, ← map_pow, hr, map_one]
    apply Units.ext
    refine Matrix.map_injective ι.injective ?_
    show (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = (1 : Matrix (Fin n) (Fin n) (Qbar l)).map ι
    rw [hM, Matrix.map_one _ (map_zero ι) (map_one ι)]

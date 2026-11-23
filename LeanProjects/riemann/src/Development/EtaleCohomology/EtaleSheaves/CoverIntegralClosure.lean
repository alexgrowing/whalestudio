import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.E.CoverIntegralClosure

theorem inj_sub (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P))) :=
  Subtype.val_injective

theorem aic_integralClosure (P : Type) [CommRing P] [IsDomain P] :
    AIC (integralClosure P (AlgebraicClosure (FractionRing P))) := by
  intro p hp hdeg
  have hdeg' : (p.map (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P)))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (inj_sub P)]
    intro h
    rw [Polynomial.degree_eq_natDegree hp.ne_zero] at h
    norm_cast at h
    omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hdeg'
  have hTa : IsIntegral (integralClosure P (AlgebraicClosure (FractionRing P))) a :=
    ⟨p, hp, by simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, Polynomial.aeval_def] using ha⟩
  have hPa : IsIntegral P a := isIntegral_trans a hTa
  have ha' : Polynomial.eval₂ (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P))) a p = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, Polynomial.aeval_def] using ha
  refine ⟨⟨a, hPa⟩, ?_⟩
  apply inj_sub P
  rw [map_zero, ← Polynomial.eval₂_at_apply]
  exact ha'

theorem inj_P (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap P (integralClosure P (AlgebraicClosure (FractionRing P)))) := by
  have h : Function.Injective (algebraMap P (AlgebraicClosure (FractionRing P))) := by
    rw [IsScalarTower.algebraMap_eq P (FractionRing P) (AlgebraicClosure (FractionRing P))]
    exact (algebraMap (FractionRing P) _).injective.comp (IsFractionRing.injective P _)
  rw [IsScalarTower.algebraMap_eq P (integralClosure P (AlgebraicClosure (FractionRing P)))
    (AlgebraicClosure (FractionRing P))] at h
  exact fun x y hxy => h (by simp only [RingHom.comp_apply, hxy])

theorem Cover_of : LateralTheory.E.t_E1Cut.Cover := by
  intro A _
  let π : MvPolynomial A ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) id
  have hπ : Function.Surjective π := fun a => ⟨MvPolynomial.X a, by simp [π]⟩
  let T := integralClosure (MvPolynomial A ℤ) (AlgebraicClosure (FractionRing (MvPolynomial A ℤ)))
  let I : Ideal T := (RingHom.ker π).map (algebraMap (MvPolynomial A ℤ) T)
  let ψ : MvPolynomial A ℤ ⧸ RingHom.ker π →+* T ⧸ I :=
    Ideal.quotientMap I (algebraMap (MvPolynomial A ℤ) T) Ideal.le_comap_map
  let φ : A →+* T ⧸ I := ψ.comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hcomp : φ.comp π = (Ideal.Quotient.mk I).comp (algebraMap (MvPolynomial A ℤ) T) := by
    apply RingHom.ext
    intro x
    simp [φ, ψ, Ideal.quotientMap_mk]
  refine ⟨T ⧸ I, inferInstance, φ, ?_, ?_, ?_⟩
  · apply RingHom.IsIntegral.tower_top π φ
    rw [hcomp]
    exact RingHom.IsIntegral.trans _ _ (fun x => Algebra.IsIntegral.isIntegral x)
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  · intro p
    have : (Ideal.comap π p.asIdeal).IsPrime := Ideal.comap_isPrime π p.asIdeal
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := T)
      (Ideal.comap π p.asIdeal) (⊥ : Ideal T) (by
        rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (inj_P _)]
        exact bot_le)
    have hIQ : I ≤ Q := by
      apply Ideal.map_le_iff_le_comap.2
      rw [hQc]
      intro x hx
      simp [RingHom.mem_ker.1 hx]
    have hQ' : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    refine ⟨⟨Q.map (Ideal.Quotient.mk I), hQ'⟩, ?_⟩
    ext1
    apply Ideal.comap_injective_of_surjective π hπ
    simp only [PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hIQ, hQc]
  · exact ⟨T, inferInstance, inferInstance, Ideal.Quotient.mk I, aic_integralClosure _,
      Ideal.Quotient.mk_surjective⟩

end LateralTheory.E.CoverIntegralClosure

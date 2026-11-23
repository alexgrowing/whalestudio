import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open MvPolynomial

namespace LateralTheory.E.EtLiftPf

set_option linter.style.haveILetI false

theorem EtLift_of : LateralTheory.E.t_E1Cut.EtLift := by
  intro T S C _ _ _ _ _ π hπ
  letI : Algebra T S := π.toAlgebra
  letI : Algebra T C := ((algebraMap S C).comp π).toAlgebra
  haveI : IsScalarTower T S C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨ι, σ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 ‹_›).out
  haveI : P.HasCoeffs T := ⟨fun x _ => hπ x⟩
  let M := P.ModelOfHasCoeffs T
  let P0 := P.toPreSubmersivePresentation.ofHasCoeffs T
  let J : M := P0.jacobian
  let C' := Localization.Away J
  let Q := Algebra.PreSubmersivePresentation.localizationAway C' J
  let R0 := Q.comp P0
  have hJu : IsUnit (algebraMap M C' J) := IsLocalization.Away.algebraMap_isUnit J
  have hJ : R0.jacobian = algebraMap M C' J * algebraMap M C' J := by
    simp only [R0, Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Q,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    rfl
  let R1 : Algebra.SubmersivePresentation T C' (Unit ⊕ ι) (Unit ⊕ σ) :=
    { R0 with jacobian_isUnit := by rw [hJ]; exact hJu.mul hJu }
  have hdim : R1.dimension = 0 := by
    have := Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension Q P0
    have hQ : Q.dimension = 0 := Algebra.Presentation.localizationAway_dimension_zero J
    have hP0 : P0.dimension = 0 := hP
    exact this.trans (by rw [hQ, hP0])
  haveI : Algebra.Etale T C' := by
    haveI := R1.isStandardSmoothOfRelativeDimension hdim
    infer_instance

  let φM : M →ₐ[T] C := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval P.val) (by
    intro a ha
    have hle : Ideal.span (Set.range (P.relationOfHasCoeffs T)) ≤
        RingHom.ker (MvPolynomial.aeval (R := T) P.val) := by
      rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩
      exact P.toPresentation.aeval_val_relationOfHasCoeffs T r
    exact hle ha)
  have hφmk : ∀ p : MvPolynomial ι T, φM (Ideal.Quotient.mk _ p) = MvPolynomial.aeval P.val p :=
    fun p => rfl
  have hφJ : φM J = P.jacobian := by
    classical
    cases nonempty_fintype σ
    rw [← P.aeval_jacobianOfHasCoeffs T]
    show φM P0.jacobian = _
    rw [P0.jacobian_eq_jacobiMatrix_det]
    unfold Algebra.SubmersivePresentation.jacobianOfHasCoeffs
    exact (hφmk _).trans (by congr 1; convert rfl)
  let ρ : C' →+* C := IsLocalization.Away.lift J (hφJ ▸ P.jacobian_isUnit)
  have hρM : ∀ m : M, ρ (algebraMap M C' m) = φM m := fun m => IsLocalization.lift_eq _ m
  refine ⟨C', inferInstance, inferInstance, ρ, inferInstance, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨q, hq⟩ := MvPolynomial.map_surjective π hπ (P.σ c)
    refine ⟨algebraMap M C' (Ideal.Quotient.mk _ q), ?_⟩
    rw [hρM, hφmk, ← MvPolynomial.aeval_map_algebraMap S]
    change MvPolynomial.aeval P.val (MvPolynomial.map π q) = c
    rw [hq, P.aeval_val_σ]
  · ext t
    show ρ (algebraMap T C' t) = _
    rw [IsScalarTower.algebraMap_apply T M C', hρM, AlgHom.commutes]
    rfl
  · let K : Ideal C' := (RingHom.ker π).map (algebraMap T C')
    have hT : ∀ t, ρ (algebraMap T C' t) = algebraMap S C (π t) := by
      intro t; rw [IsScalarTower.algebraMap_apply T M C', hρM, AlgHom.commutes]; rfl
    apply le_antisymm
    swap
    · rw [Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, RingHom.mem_ker, hT, RingHom.mem_ker.1 ht, map_zero]
    let e := RingHom.quotientKerEquivOfSurjective hπ
    let θ : S →+* C' ⧸ K :=
      (Ideal.quotientMap K (algebraMap T C') Ideal.le_comap_map).comp e.symm.toRingHom
    have hθ : ∀ t, θ (π t) = Ideal.Quotient.mk K (algebraMap T C' t) := by
      intro t
      have : e.symm (π t) = Ideal.Quotient.mk _ t := by
        rw [RingEquiv.symm_apply_eq]; rfl
      show Ideal.quotientMap K (algebraMap T C') Ideal.le_comap_map (e.symm (π t)) = _
      rw [this, Ideal.quotientMap_mk]
    let xv : ι → C' ⧸ K := fun i => Ideal.Quotient.mk K (algebraMap M C' (Ideal.Quotient.mk _ (X i)))
    let χ : MvPolynomial ι S →+* C' ⧸ K := MvPolynomial.eval₂Hom θ xv
    have hkey : ∀ q : MvPolynomial ι T, χ (MvPolynomial.map π q) =
        Ideal.Quotient.mk K (algebraMap M C' (Ideal.Quotient.mk _ q)) := by
      intro q
      have h2 : χ.comp (MvPolynomial.map π) =
          ((Ideal.Quotient.mk K).comp (algebraMap M C')).comp (Ideal.Quotient.mk _) := by
        apply MvPolynomial.ringHom_ext
        · intro t
          simp only [RingHom.comp_apply, MvPolynomial.map_C, χ, MvPolynomial.coe_eval₂Hom,
            MvPolynomial.eval₂_C, hθ]
          rw [IsScalarTower.algebraMap_apply T M C']
          rfl
        · intro i
          simp [χ, xv]
      exact RingHom.congr_fun h2 q
    have hker : ∀ a ∈ P.ker, χ a = 0 := by
      intro a ha
      rw [← P.span_range_relation_eq_ker] at ha
      have hle : Ideal.span (Set.range P.relation) ≤ RingHom.ker χ := by
        rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, ← P.toPresentation.map_relationOfHasCoeffs T r]
        change χ (MvPolynomial.map π _) = 0
        rw [hkey, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self r)), map_zero, map_zero]
      exact hle ha
    let ψ : C →+* C' ⧸ K := (Ideal.Quotient.lift P.ker χ hker).comp P.quotientEquiv.symm.toRingHom
    have hψP : ∀ p, ψ (algebraMap P.Ring C p) = χ p := by
      intro p
      show Ideal.Quotient.lift P.ker χ hker (P.quotientEquiv.symm (algebraMap _ _ p)) = χ p
      rw [← P.quotientEquiv_mk, AlgEquiv.symm_apply_apply]
      rfl
    have hψ : ψ.comp ρ = Ideal.Quotient.mk K := by
      apply IsLocalization.ringHom_ext (Submonoid.powers J)
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun q => ?_
      simp only [RingHom.comp_apply]
      rw [hρM, hφmk, ← MvPolynomial.aeval_map_algebraMap S, ← hkey, ← hψP,
        Algebra.Generators.algebraMap_apply]
      rfl
    intro z hz
    rw [RingHom.mem_ker] at hz
    have h3 := RingHom.congr_fun hψ z
    simp only [RingHom.comp_apply, hz, map_zero] at h3
    exact Ideal.Quotient.eq_zero_iff_mem.1 h3.symm

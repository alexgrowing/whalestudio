import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.Blowup

universe u

variable {R : Type u} [CommRing R]

private theorem reesGenerator_coe_eq_C_mul_X (I : Ideal R) (a : ↥I) :
    ((reesGenerator I a : ↥(reesAlgebra I)) : Polynomial R) =
      Polynomial.C (a : R) * Polynomial.X := by
  rw [reesGenerator_coe, ← Polynomial.C_mul_X_pow_eq_monomial, pow_one]

private theorem localization_mk_eq_zero_iff {A : Type u} [CommRing A] {M : Submonoid A} (x : A)
    (s : ↥M) : Localization.mk x s = (0 : Localization M) ↔ ∃ c : ↥M, (c : A) * x = 0 := by
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_eq_zero_iff x s

noncomputable def affineBlowup (I : Ideal R) : Scheme.{u} :=
  AlgebraicGeometry.Proj (reesGrading I)

theorem affineBlowup_eq_proj (I : Ideal R) :
    affineBlowup I = AlgebraicGeometry.Proj (reesGrading I) := rfl

namespace AffineBlowup

noncomputable def toSpec (I : Ideal R) :
    affineBlowup I ⟶ AlgebraicGeometry.Spec (CommRingCat.of R) :=
  AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0)))

theorem toSpec_eq_toSpecZero_comp (I : Ideal R) :
    toSpec I =
      AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0))) := rfl

end AffineBlowup

noncomputable def affineBlowupChart (I : Ideal R) (a : ↥I) :
    AlgebraicGeometry.Spec
        (CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))) ⟶
      affineBlowup I :=
  AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
    Nat.one_pos

theorem affineBlowupChart_eq_awayι (I : Ideal R) (a : ↥I) :
    affineBlowupChart I a =
      AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
        Nat.one_pos := rfl

instance instIsOpenImmersionAffineBlowupChart (I : Ideal R) (a : ↥I) :
    AlgebraicGeometry.IsOpenImmersion (affineBlowupChart I a) :=
  inferInstanceAs (AlgebraicGeometry.IsOpenImmersion
    (AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
      Nat.one_pos))

theorem opensRange_affineBlowupChart_eq_basicOpen (I : Ideal R) (a : ↥I) :
    (affineBlowupChart I a).opensRange =
      AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :=
  AlgebraicGeometry.Proj.opensRange_awayι ..

theorem iSup_proj_basicOpen_reesGenerator_eq_top (I : Ideal R) :
    (⨆ a : ↥I, AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a)) = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
  exact reesGrading_irrelevant_le_span I

private theorem exists_mem_range_affineBlowupChart (I : Ideal R) (x : ↥(affineBlowup I)) :
    ∃ a : ↥I, x ∈ Set.range (affineBlowupChart I a).base := by
  have h2 : (⋃ a : ↥I,
      ((AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :
          (AlgebraicGeometry.Proj (reesGrading I)).Opens) :
        Set ↥(AlgebraicGeometry.Proj (reesGrading I)))) = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_iSup, iSup_proj_basicOpen_reesGenerator_eq_top]
    simp
  have hx : x ∈ (⋃ a : ↥I,
      ((AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :
          (AlgebraicGeometry.Proj (reesGrading I)).Opens) :
        Set ↥(AlgebraicGeometry.Proj (reesGrading I)))) := by
    rw [h2]
    exact Set.mem_univ _
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  refine ⟨a, ?_⟩
  have hs : Set.range (affineBlowupChart I a).base =
      ((AlgebraicGeometry.Proj.basicOpen (reesGrading I) (reesGenerator I a) :
          (AlgebraicGeometry.Proj (reesGrading I)).Opens) :
        Set ↥(AlgebraicGeometry.Proj (reesGrading I))) :=
    congrArg (fun U : (affineBlowup I).Opens => (U : Set ↥(affineBlowup I)))
      (opensRange_affineBlowupChart_eq_basicOpen I a)
  rw [hs]
  exact ha

noncomputable def affineBlowupAffineOpenCover (I : Ideal R) : (affineBlowup I).AffineOpenCover where
  I₀ := ↥I
  X a := CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))
  f a := affineBlowupChart I a
  idx x := (exists_mem_range_affineBlowupChart I x).choose
  covers x := (exists_mem_range_affineBlowupChart I x).choose_spec
  map_prop a := instIsOpenImmersionAffineBlowupChart I a

noncomputable def chartRingHom (I : Ideal R) (a : ↥I) :
    R →+* HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a) :=
  (HomogeneousLocalization.fromZeroRingHom (reesGrading I)
      (Submonoid.powers (reesGenerator I a))).comp
    ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0))

theorem chartRingHom_apply (I : Ideal R) (a : ↥I) (r : R) :
    chartRingHom I a r =
      HomogeneousLocalization.fromZeroRingHom (reesGrading I) (Submonoid.powers (reesGenerator I a))
        (reesDegreeZeroEquiv I r) := rfl

private theorem val_chartRingHom (I : Ideal R) (a : ↥I) (r : R) :
    HomogeneousLocalization.val (chartRingHom I a r) =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)))
        (1 : ↥(Submonoid.powers (reesGenerator I a))) := rfl

noncomputable instance AffineBlowup.instAlgebraChart (I : Ideal R) (a : ↥I) :
    Algebra R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :=
  RingHom.toAlgebra (chartRingHom I a)

theorem algebraMap_chart_eq_chartRingHom (I : Ideal R) (a : ↥I) :
    @algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
        (AffineBlowup.instAlgebraChart I a) =
      chartRingHom I a := rfl

theorem algebraMap_chart_apply (I : Ideal R) (a : ↥I) (r : R) :
    @algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
        (AffineBlowup.instAlgebraChart I a) r =
      chartRingHom I a r := rfl

theorem affineBlowupChart_comp_toSpec (I : Ideal R) (a : ↥I) :
    affineBlowupChart I a ≫ AffineBlowup.toSpec I =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (@algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
            (AffineBlowup.instAlgebraChart I a))) := by
  show AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
        Nat.one_pos ≫
      (AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0)))) =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (@algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
            (AffineBlowup.instAlgebraChart I a)))
  rw [← Category.assoc, AlgebraicGeometry.Proj.awayι_toSpecZero,
    ← AlgebraicGeometry.Spec.map_comp]
  rfl

private theorem reesGenerator_pow_one_mem_reesGrading_one (I : Ideal R) (a : ↥I) :
    reesGenerator I a ^ 1 ∈ reesGrading I 1 := by
  rw [pow_one]
  exact reesGenerator_mem_reesGrading I a

private theorem reesGenerator_pow_one_mem_powers (I : Ideal R) (a : ↥I) :
    reesGenerator I a ^ 1 ∈ Submonoid.powers (reesGenerator I a) :=
  Submonoid.pow_mem _ (Submonoid.mem_powers _) 1

noncomputable def chartFraction (I : Ideal R) (a b : ↥I) :
    HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a) :=
  HomogeneousLocalization.mk
    { deg := 1
      num := ⟨reesGenerator I b, reesGenerator_mem_reesGrading I b⟩
      den := ⟨reesGenerator I a ^ 1, reesGenerator_pow_one_mem_reesGrading_one I a⟩
      den_mem := reesGenerator_pow_one_mem_powers I a }

theorem chartFraction_eq_mk (I : Ideal R) (a b : ↥I) :
    chartFraction I a b =
      HomogeneousLocalization.mk
        { deg := 1
          num := ⟨reesGenerator I b, reesGenerator_mem_reesGrading I b⟩
          den := ⟨reesGenerator I a ^ 1, reesGenerator_pow_one_mem_reesGrading_one I a⟩
          den_mem := reesGenerator_pow_one_mem_powers I a } := rfl

theorem chartRingHom_coe_eq_chartFraction_mul (I : Ideal R) (a b : ↥I) :
    chartRingHom I a (b : R) = chartFraction I a b * chartRingHom I a (a : R) := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    val_chartRingHom, val_chartRingHom, chartFraction_eq_mk, HomogeneousLocalization.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [reesGenerator_coe_eq_C_mul_X, reesDegreeZeroEquiv_coe_coe]
  ring

theorem map_chartRingHom_eq_span_singleton (I : Ideal R) (a : ↥I) :
    Ideal.map (chartRingHom I a) I = Ideal.span {chartRingHom I a (a : R)} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨chartFraction I a ⟨x, hx⟩, (chartRingHom_coe_eq_chartFraction_mul I a ⟨x, hx⟩).symm⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ a.2

theorem chartRingHom_mem_nonZeroDivisors (I : Ideal R) (a : ↥I) :
    chartRingHom I a (a : R) ∈
      nonZeroDivisors (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) := by
  have key : ∀ z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a),
      chartRingHom I a (a : R) * z = 0 → z = 0 := by
    intro z hz
    have hz' : HomogeneousLocalization.val (chartRingHom I a (a : R) * z) = 0 := by
      rw [hz, HomogeneousLocalization.val_zero]
    rw [HomogeneousLocalization.val_mul, val_chartRingHom,
      HomogeneousLocalization.eq_num_div_den z, Localization.mk_mul,
      localization_mk_eq_zero_iff] at hz'
    obtain ⟨c, hc⟩ := hz'
    obtain ⟨m, hm⟩ : ∃ m : ℕ, reesGenerator I a ^ m = (c : ↥(reesAlgebra I)) := c.2
    rw [← hm] at hc
    have hP : reesGenerator I a ^ (m + 1) * HomogeneousLocalization.num z = 0 := by
      apply Subtype.ext
      have h1 := congrArg (fun p : ↥(reesAlgebra I) => (p : Polynomial R)) hc
      push_cast [reesGenerator_coe_eq_C_mul_X, reesDegreeZeroEquiv_coe_coe] at h1
      push_cast [reesGenerator_coe_eq_C_mul_X]
      linear_combination (Polynomial.X : Polynomial R) * h1
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_zero,
      HomogeneousLocalization.eq_num_div_den z, localization_mk_eq_zero_iff]
    exact ⟨⟨reesGenerator I a ^ (m + 1), Submonoid.pow_mem _ (Submonoid.mem_powers _) (m + 1)⟩, hP⟩
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun z hz => key z ((mul_comm (chartRingHom I a (a : R)) z).trans hz)⟩

end FunctorialResolution.Blowup

import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversalLift
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupChartPreimages
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

universe u v

def coordIdeal (R : Type u) [CommRing R] {σ : Type v} (S : Finset σ) : Ideal (MvPolynomial σ R) :=
  Ideal.span ((MvPolynomial.X : σ → MvPolynomial σ R) '' (S : Set σ))

theorem coordIdeal_eq_span (R : Type u) [CommRing R] {σ : Type v} (S : Finset σ) :
    coordIdeal R S = Ideal.span ((MvPolynomial.X : σ → MvPolynomial σ R) '' (S : Set σ)) := rfl

theorem X_mem_coordIdeal (R : Type u) [CommRing R] {σ : Type v} (S : Finset σ) {i : σ}
    (hi : i ∈ S) : (MvPolynomial.X i : MvPolynomial σ R) ∈ coordIdeal R S :=
  Ideal.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩

def coordIdealGen (R : Type u) [CommRing R] {σ : Type v} (S : Finset σ) (i : σ) (hi : i ∈ S) :
    ↥(coordIdeal R S) :=
  ⟨MvPolynomial.X i, X_mem_coordIdeal R S hi⟩

@[simp] theorem coe_coordIdealGen (R : Type u) [CommRing R] {σ : Type v} (S : Finset σ) (i : σ)
    (hi : i ∈ S) :
    ((coordIdealGen R S i hi : ↥(coordIdeal R S)) : MvPolynomial σ R) = MvPolynomial.X i := rfl

private theorem reesGenerator_mem_of_span {A : Type u} [CommRing A] (s : Set A)
    (P : Ideal ↥(reesAlgebra (Ideal.span s)))
    (hP : ∀ y ∈ s, ∀ hy : y ∈ Ideal.span s, Blowup.reesGenerator (Ideal.span s) ⟨y, hy⟩ ∈ P)
    (a : ↥(Ideal.span s)) : Blowup.reesGenerator (Ideal.span s) a ∈ P := by
  obtain ⟨r, hr⟩ := a
  induction hr using Submodule.span_induction with
  | mem x hx => exact hP x hx _
  | zero =>
      have e : Blowup.reesGenerator (Ideal.span s) (0 : ↥(Ideal.span s)) = 0 := by
        apply Subtype.ext
        simp [Blowup.reesGenerator_coe]
      show Blowup.reesGenerator (Ideal.span s) (0 : ↥(Ideal.span s)) ∈ P
      rw [e]
      exact P.zero_mem
  | add x y hx hy ihx ihy =>
      have e : Blowup.reesGenerator (Ideal.span s) ((⟨x, hx⟩ : ↥(Ideal.span s)) + ⟨y, hy⟩)
          = Blowup.reesGenerator (Ideal.span s) ⟨x, hx⟩ + Blowup.reesGenerator (Ideal.span s) ⟨y, hy⟩ := by
        apply Subtype.ext
        simp [Blowup.reesGenerator_coe]
      show Blowup.reesGenerator (Ideal.span s) ((⟨x, hx⟩ : ↥(Ideal.span s)) + ⟨y, hy⟩) ∈ P
      rw [e]
      exact P.add_mem ihx ihy
  | smul c x hx ih =>
      have e : Blowup.reesGenerator (Ideal.span s) (c • (⟨x, hx⟩ : ↥(Ideal.span s)))
          = c • Blowup.reesGenerator (Ideal.span s) ⟨x, hx⟩ := by
        apply Subtype.ext
        simp [Blowup.reesGenerator_coe, Polynomial.smul_monomial, smul_eq_mul]
      show Blowup.reesGenerator (Ideal.span s) (c • (⟨x, hx⟩ : ↥(Ideal.span s))) ∈ P
      rw [e, Algebra.smul_def]
      exact Ideal.mul_mem_left P _ ih

private theorem reesGenerator_mem_homogeneousIdeal_of_span {A : Type u} [CommRing A] (s : Set A)
    (P : HomogeneousIdeal (Blowup.reesGrading (Ideal.span s)))
    (hP : ∀ y ∈ s, ∀ hy : y ∈ Ideal.span s, Blowup.reesGenerator (Ideal.span s) ⟨y, hy⟩ ∈ P)
    (a : ↥(Ideal.span s)) : Blowup.reesGenerator (Ideal.span s) a ∈ P :=
  reesGenerator_mem_of_span s P.toIdeal (fun y hy hy2 => hP y hy hy2) a

theorem iSup_opensRange_affineBlowupChart_coordIdealGen (R : Type u) [CommRing R] {σ : Type v}
    (S : Finset σ) :
    (⨆ i : ↥S, Scheme.Hom.opensRange
        (Blowup.affineBlowupChart (coordIdeal R S) (coordIdealGen R S i.1 i.2)))
      = (⊤ : (Blowup.affineBlowup (coordIdeal R S)).Opens) := by
  refine le_antisymm le_top ?_
  rw [SetLike.le_def]
  intro x _
  have hxtop : x ∈ (⨆ a : ↥(coordIdeal R S),
      Proj.basicOpen (Blowup.reesGrading (coordIdeal R S)) (Blowup.reesGenerator (coordIdeal R S) a)) := by
    rw [Blowup.iSup_proj_basicOpen_reesGenerator_eq_top]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hxtop
  by_contra hxn
  refine (Proj.mem_basicOpen ..).mp ha ?_
  refine reesGenerator_mem_homogeneousIdeal_of_span
    ((MvPolynomial.X : σ → MvPolynomial σ R) '' (S : Set σ)) _ ?_ a
  intro y hy hy2
  obtain ⟨i, hiS, rfl⟩ := hy
  by_contra hcon
  refine hxn (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, Finset.mem_coe.mp hiS⟩, ?_⟩)
  rw [Blowup.opensRange_affineBlowupChart_eq_basicOpen]
  exact (Proj.mem_basicOpen ..).mpr hcon

theorem X_mem_nonZeroDivisors (R : Type u) [CommRing R] {σ : Type v} (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ R) ∈ nonZeroDivisors (MvPolynomial σ R) := by
  have key : ∀ x : MvPolynomial σ R, x * MvPolynomial.X i = 0 → x = 0 := by
    intro x hx
    ext m
    have h := MvPolynomial.coeff_mul_X m i x
    rw [hx, MvPolynomial.coeff_zero] at h
    simp [← h]
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

def coordBlowupSubst (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (S : Finset σ) (s : σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval fun i =>
    if i ∈ S ∧ i ≠ s then (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s
    else MvPolynomial.X i

theorem coordBlowupSubst_X (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (S : Finset σ)
    (s : σ) (i : σ) :
    coordBlowupSubst R S s (MvPolynomial.X i) =
      if i ∈ S ∧ i ≠ s then (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s
      else MvPolynomial.X i :=
  MvPolynomial.aeval_X _ i

@[simp] theorem coordBlowupSubst_X_of_mem (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) {i : σ} (hi : i ∈ S) (hne : i ≠ s) :
    coordBlowupSubst R S s (MvPolynomial.X i) =
      (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s := by
  rw [coordBlowupSubst_X, if_pos ⟨hi, hne⟩]

@[simp] theorem coordBlowupSubst_X_self (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) :
    coordBlowupSubst R S s (MvPolynomial.X s) = (MvPolynomial.X s : MvPolynomial σ R) := by
  rw [coordBlowupSubst_X, if_neg]
  rintro ⟨-, h⟩
  exact h rfl

@[simp] theorem coordBlowupSubst_X_of_not_mem_erase (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) {i : σ} (h : ¬ (i ∈ S ∧ i ≠ s)) :
    coordBlowupSubst R S s (MvPolynomial.X i) = (MvPolynomial.X i : MvPolynomial σ R) := by
  rw [coordBlowupSubst_X, if_neg h]

theorem coordBlowupSubst_C (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (r : R) :
    coordBlowupSubst R S s (MvPolynomial.C r) = (MvPolynomial.C r : MvPolynomial σ R) := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (coordBlowupSubst R S s).commutes r

theorem map_coordIdeal_coordBlowupSubst (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    Ideal.map (coordBlowupSubst R S s).toRingHom (coordIdeal R S)
      = Ideal.span {(MvPolynomial.X s : MvPolynomial σ R)} := by
  apply le_antisymm
  · rw [coordIdeal_eq_span, Ideal.map_span, Ideal.span_le]
    rintro y ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    show (coordBlowupSubst R S s).toRingHom (MvPolynomial.X i) ∈
      Ideal.span {(MvPolynomial.X s : MvPolynomial σ R)}
    by_cases h : i ∈ S ∧ i ≠ s
    · rw [show (coordBlowupSubst R S s).toRingHom (MvPolynomial.X i)
          = (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s from
        coordBlowupSubst_X_of_mem R S s h.1 h.2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · have hieq : i = s := by
        by_contra hne
        exact h ⟨Finset.mem_coe.mp hi, hne⟩
      rw [show (coordBlowupSubst R S s).toRingHom (MvPolynomial.X i)
          = (MvPolynomial.X i : MvPolynomial σ R) from coordBlowupSubst_X_of_not_mem_erase R S s h, hieq]
      exact Ideal.mem_span_singleton_self _
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h1 : (MvPolynomial.X s : MvPolynomial σ R) ∈ coordIdeal R S := X_mem_coordIdeal R S hs
    have h2 := Ideal.mem_map_of_mem ((coordBlowupSubst R S s).toRingHom) h1
    rw [show (coordBlowupSubst R S s).toRingHom (MvPolynomial.X s)
        = (MvPolynomial.X s : MvPolynomial σ R) from coordBlowupSubst_X_self R S s] at h2
    exact h2

private theorem coe_reesDegreeZeroEquiv {A : Type u} [CommRing A] (I : Ideal A) (r : A) :
    ((Blowup.reesDegreeZeroEquiv I r : ↥(Blowup.reesGrading I 0)) : ↥(reesAlgebra I))
      = algebraMap A ↥(reesAlgebra I) r := by
  apply Subtype.ext
  rw [Blowup.reesDegreeZeroEquiv_coe_coe]
  simp [Polynomial.C_eq_algebraMap]

private def coordIdealReesAlgebraLift (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    ↥(reesAlgebra (coordIdeal R S)) →+* MvPolynomial σ R :=
  Blowup.reesAlgebraLift (coordIdeal R S) (coordBlowupSubst R S s).toRingHom (MvPolynomial.X s)
    (map_coordIdeal_coordBlowupSubst R S s hs) (X_mem_nonZeroDivisors R s)

private theorem reesAlgebraToMvPolynomial_algebraMap (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) (r : MvPolynomial σ R) :
    coordIdealReesAlgebraLift R S s hs (algebraMap (MvPolynomial σ R) ↥(reesAlgebra (coordIdeal R S)) r)
      = coordBlowupSubst R S s r :=
  Blowup.reesAlgebraLift_algebraMap (coordIdeal R S) (coordBlowupSubst R S s).toRingHom (MvPolynomial.X s)
    (map_coordIdeal_coordBlowupSubst R S s hs) (X_mem_nonZeroDivisors R s) r

private theorem reesAlgebraToMvPolynomial_reesGenerator (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    coordIdealReesAlgebraLift R S s hs (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) = 1 :=
  Blowup.reesAlgebraLift_reesGenerator (coordIdeal R S) (coordBlowupSubst R S s).toRingHom (MvPolynomial.X s)
    (map_coordIdeal_coordBlowupSubst R S s hs) (X_mem_nonZeroDivisors R s)
    (coordIdealGen R S s hs) (by rw [coe_coordIdealGen]; exact coordBlowupSubst_X_self R S s)

private theorem isUnit_reesAlgebraToMvPolynomial_powers (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    ∀ y : ↥(Submonoid.powers (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs))),
      IsUnit (coordIdealReesAlgebraLift R S s hs (y : ↥(reesAlgebra (coordIdeal R S)))) := by
  rintro ⟨y, n, rfl⟩
  show IsUnit (coordIdealReesAlgebraLift R S s hs
    ((Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) ^ n))
  rw [map_pow, reesAlgebraToMvPolynomial_reesGenerator, one_pow]
  exact isUnit_one

private def homogeneousAwayToLocalization {A : Type u} [CommRing A] (I : Ideal A) (a : ↥I) :
    HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a) →+*
      Localization (Submonoid.powers (Blowup.reesGenerator I a)) :=
  algebraMap (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a))
    (Localization (Submonoid.powers (Blowup.reesGenerator I a)))

private theorem homogeneousLocalizationVal_apply {A : Type u} [CommRing A] (I : Ideal A) (a : ↥I)
    (z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :
    homogeneousAwayToLocalization I a z = HomogeneousLocalization.val z :=
  HomogeneousLocalization.algebraMap_apply ..

private def coordBlowupChartToMvPolynomial (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) →+* MvPolynomial σ R :=
  (IsLocalization.lift (isUnit_reesAlgebraToMvPolynomial_powers R S s hs)).comp
    (homogeneousAwayToLocalization (coordIdeal R S) (coordIdealGen R S s hs))

private theorem chartToMvPolynomial_apply (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S)
    (z : HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
      (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs))) :
    coordBlowupChartToMvPolynomial R S s hs z =
      IsLocalization.lift (isUnit_reesAlgebraToMvPolynomial_powers R S s hs) (HomogeneousLocalization.val z) := by
  show IsLocalization.lift (isUnit_reesAlgebraToMvPolynomial_powers R S s hs)
      (homogeneousAwayToLocalization (coordIdeal R S) (coordIdealGen R S s hs) z) = _
  rw [homogeneousLocalizationVal_apply]

private theorem chartToMvPolynomial_chartRingHom (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) (r : MvPolynomial σ R) :
    coordBlowupChartToMvPolynomial R S s hs (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) r)
      = coordBlowupSubst R S s r := by
  have hval : HomogeneousLocalization.val (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) r)
      = Localization.mk
          ((Blowup.reesDegreeZeroEquiv (coordIdeal R S) r : ↥(reesAlgebra (coordIdeal R S)))) 1 := rfl
  rw [chartToMvPolynomial_apply, hval, Localization.mk_eq_mk', IsLocalization.mk'_one,
    IsLocalization.lift_eq, coe_reesDegreeZeroEquiv, reesAlgebraToMvPolynomial_algebraMap]

private def mvPolynomialToCoordBlowupChart (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    MvPolynomial σ R →+* HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
      (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) :=
  MvPolynomial.eval₂Hom
    ((Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)).comp
      (MvPolynomial.C : R →+* MvPolynomial σ R))
    (fun i => if h : i ∈ S ∧ i ≠ s then
        Blowup.chartFraction (coordIdeal R S) (coordIdealGen R S s hs) (coordIdealGen R S i h.1)
      else Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X i))

private theorem awayCoordGenEquivMvPolynomial_invFun_C (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) (r : R) :
    mvPolynomialToCoordBlowupChart R S s hs (MvPolynomial.C r)
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.C r) :=
  MvPolynomial.eval₂Hom_C _ _ r

private theorem awayCoordGenEquivMvPolynomial_invFun_X (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) (i : σ) :
    mvPolynomialToCoordBlowupChart R S s hs (MvPolynomial.X i)
      = if h : i ∈ S ∧ i ≠ s then
          Blowup.chartFraction (coordIdeal R S) (coordIdealGen R S s hs) (coordIdealGen R S i h.1)
        else Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom_X' _ _ i

private theorem awayCoordGenEquivMvPolynomial_invFun_X_self (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    mvPolynomialToCoordBlowupChart R S s hs (MvPolynomial.X s)
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) := by
  rw [awayCoordGenEquivMvPolynomial_invFun_X, dif_neg]
  rintro ⟨-, h⟩
  exact h rfl

private theorem mvPolynomialToChart_coordBlowupSubst (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) (f : MvPolynomial σ R) :
    mvPolynomialToCoordBlowupChart R S s hs (coordBlowupSubst R S s f)
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) f := by
  have key : (mvPolynomialToCoordBlowupChart R S s hs).comp ((coordBlowupSubst R S s).toRingHom)
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      show mvPolynomialToCoordBlowupChart R S s hs (coordBlowupSubst R S s (MvPolynomial.C r)) = _
      rw [coordBlowupSubst_C, awayCoordGenEquivMvPolynomial_invFun_C]
    · intro i
      show mvPolynomialToCoordBlowupChart R S s hs (coordBlowupSubst R S s (MvPolynomial.X i)) = _
      by_cases h : i ∈ S ∧ i ≠ s
      · rw [coordBlowupSubst_X_of_mem R S s h.1 h.2, map_mul, awayCoordGenEquivMvPolynomial_invFun_X, dif_pos h, awayCoordGenEquivMvPolynomial_invFun_X_self]
        have hb := Blowup.chartRingHom_coe_eq_chartFraction_mul (coordIdeal R S) (coordIdealGen R S s hs)
          (coordIdealGen R S i h.1)
        rw [coe_coordIdealGen, coe_coordIdealGen] at hb
        exact hb.symm
      · rw [coordBlowupSubst_X_of_not_mem_erase R S s h, awayCoordGenEquivMvPolynomial_invFun_X, dif_neg h]
  exact DFunLike.congr_fun key f

private theorem chartToMvPolynomial_mvPolynomialToChart (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) (f : MvPolynomial σ R) :
    coordBlowupChartToMvPolynomial R S s hs (mvPolynomialToCoordBlowupChart R S s hs f) = f := by
  have key : (coordBlowupChartToMvPolynomial R S s hs).comp (mvPolynomialToCoordBlowupChart R S s hs) = RingHom.id (MvPolynomial σ R) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      show coordBlowupChartToMvPolynomial R S s hs (mvPolynomialToCoordBlowupChart R S s hs (MvPolynomial.C r)) = MvPolynomial.C r
      rw [awayCoordGenEquivMvPolynomial_invFun_C, chartToMvPolynomial_chartRingHom, coordBlowupSubst_C]
    · intro i
      show coordBlowupChartToMvPolynomial R S s hs (mvPolynomialToCoordBlowupChart R S s hs (MvPolynomial.X i)) = MvPolynomial.X i
      by_cases h : i ∈ S ∧ i ≠ s
      · rw [awayCoordGenEquivMvPolynomial_invFun_X, dif_pos h]
        have hb := Blowup.chartRingHom_coe_eq_chartFraction_mul (coordIdeal R S) (coordIdealGen R S s hs)
          (coordIdealGen R S i h.1)
        rw [coe_coordIdealGen, coe_coordIdealGen] at hb
        have h2 := congrArg (coordBlowupChartToMvPolynomial R S s hs) hb
        rw [chartToMvPolynomial_chartRingHom, map_mul, chartToMvPolynomial_chartRingHom,
          coordBlowupSubst_X_of_mem R S s h.1 h.2, coordBlowupSubst_X_self] at h2
        have hnzd := X_mem_nonZeroDivisors R s
        exact (mul_cancel_right_mem_nonZeroDivisors hnzd).mp h2.symm
      · rw [awayCoordGenEquivMvPolynomial_invFun_X, dif_neg h, chartToMvPolynomial_chartRingHom, coordBlowupSubst_X_of_not_mem_erase R S s h]
  exact DFunLike.congr_fun key f

private theorem mvPolynomialToChart_surjective (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) : Function.Surjective (mvPolynomialToCoordBlowupChart R S s hs) := by
  intro z
  obtain ⟨n, r, hr⟩ := Blowup.exists_mul_pow_eq_chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) z
  have hLc : coordBlowupChartToMvPolynomial R S s hs
      (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)
        ((coordIdealGen R S s hs : ↥(coordIdeal R S)) : MvPolynomial σ R))
      = (MvPolynomial.X s : MvPolynomial σ R) := by
    rw [chartToMvPolynomial_chartRingHom, coe_coordIdealGen, coordBlowupSubst_X_self]
  have hpL : coordBlowupChartToMvPolynomial R S s hs
      (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)
        ((coordIdealGen R S s hs : ↥(coordIdeal R S)) : MvPolynomial σ R) ^ n)
      = coordBlowupChartToMvPolynomial R S s hs
        (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)
          ((coordIdealGen R S s hs : ↥(coordIdeal R S)) : MvPolynomial σ R)) ^ n :=
    map_pow (coordBlowupChartToMvPolynomial R S s hs)
      (Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs)
        ((coordIdealGen R S s hs : ↥(coordIdeal R S)) : MvPolynomial σ R)) n
  have h2 : coordBlowupChartToMvPolynomial R S s hs z * (MvPolynomial.X s : MvPolynomial σ R) ^ n
      = coordBlowupSubst R S s r := by
    have hcg := congrArg (coordBlowupChartToMvPolynomial R S s hs) hr
    rw [map_mul, hpL, hLc, chartToMvPolynomial_chartRingHom] at hcg
    exact hcg
  have hpF : mvPolynomialToCoordBlowupChart R S s hs ((MvPolynomial.X s : MvPolynomial σ R) ^ n)
      = mvPolynomialToCoordBlowupChart R S s hs (MvPolynomial.X s) ^ n :=
    map_pow (mvPolynomialToCoordBlowupChart R S s hs) (MvPolynomial.X s) n
  have h3 : mvPolynomialToCoordBlowupChart R S s hs (coordBlowupChartToMvPolynomial R S s hs z) *
      Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ^ n
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) r := by
    have hcg := congrArg (mvPolynomialToCoordBlowupChart R S s hs) h2
    rw [map_mul, hpF, awayCoordGenEquivMvPolynomial_invFun_X_self, mvPolynomialToChart_coordBlowupSubst] at hcg
    exact hcg
  have hnzd0 : Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ∈
      nonZeroDivisors (HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs))) :=
    Blowup.chartRingHom_mem_nonZeroDivisors (coordIdeal R S) (coordIdealGen R S s hs)
  have hnzd : Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ^ n ∈
      nonZeroDivisors (HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs))) :=
    pow_mem hnzd0 n
  refine ⟨coordBlowupChartToMvPolynomial R S s hs z, ?_⟩
  have h : mvPolynomialToCoordBlowupChart R S s hs (coordBlowupChartToMvPolynomial R S s hs z) *
      Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ^ n
      = z * Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) ^ n := by
    rw [h3]
    exact hr.symm
  exact (mul_cancel_right_mem_nonZeroDivisors hnzd).mp h

private theorem exists_ringEquiv_away_mvPolynomial (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    ∃ e : HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) ≃+* MvPolynomial σ R,
      e.symm.toRingHom.comp (coordBlowupSubst R S s).toRingHom
        = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) := by
  have hL : Function.LeftInverse (coordBlowupChartToMvPolynomial R S s hs) (mvPolynomialToCoordBlowupChart R S s hs) :=
    fun f => chartToMvPolynomial_mvPolynomialToChart R S s hs f
  refine ⟨(RingEquiv.ofBijective (mvPolynomialToCoordBlowupChart R S s hs)
      ⟨hL.injective, mvPolynomialToChart_surjective R S s hs⟩).symm, ?_⟩
  rw [RingEquiv.symm_symm]
  refine RingHom.ext fun f => ?_
  exact mvPolynomialToChart_coordBlowupSubst R S s hs f

def awayCoordGenEquivMvPolynomial (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ] (S : Finset σ) (s : σ)
    (hs : s ∈ S) :
    HomogeneousLocalization.Away (Blowup.reesGrading (coordIdeal R S))
        (Blowup.reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) ≃+* MvPolynomial σ R :=
  (exists_ringEquiv_away_mvPolynomial R S s hs).choose

theorem awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    (awayCoordGenEquivMvPolynomial R S s hs).symm.toRingHom.comp (coordBlowupSubst R S s).toRingHom
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) :=
  (exists_ringEquiv_away_mvPolynomial R S s hs).choose_spec

end FunctorialResolution.EmbeddedResolution

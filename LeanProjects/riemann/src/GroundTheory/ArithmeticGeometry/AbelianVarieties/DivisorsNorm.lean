import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.Divisors

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain

open scoped nonZeroDivisors

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

theorem finrank_coordinateRing : Module.finrank F[X] W.toAffine.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (CoordinateRing.basis W.toAffine)).trans (Fintype.card_fin 2)

theorem algebraMap_X_sub_C (x : F) :
    algebraMap F[X] W.toAffine.CoordinateRing (X - C x) = XClass W.toAffine x := by
  simp only [XClass, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem XIdeal_eq_map (x : F) : XIdeal W.toAffine x =
    (Ideal.span {X - C x}).map (algebraMap F[X] W.toAffine.CoordinateRing) := by
  rw [XIdeal, Ideal.map_span, Set.image_singleton, algebraMap_X_sub_C]

theorem span_X_sub_C_le_comap_XYIdeal (x : F) (y : F[X]) :
    Ideal.span {X - C x} ≤ (XYIdeal W.toAffine x y).comap (algebraMap F[X] _) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    algebraMap_X_sub_C]
  exact Ideal.subset_span (Set.mem_insert _ _)

variable [IsAlgClosed F] [W.IsElliptic]

theorem relNorm_XYIdeal {x y : F} (h : W.toAffine.Nonsingular x y) :
    Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y)) = Ideal.span {X - C x} := by
  have hq : (Ideal.span {X - C x} : Ideal F[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C x)
  have hle : ∀ {y' : F}, W.toAffine.Nonsingular x y' →
      Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y')) ≤ Ideal.span {X - C x} := by
    intro y' h'
    refine (Ideal.relNorm_le_comap F[X] _).trans ?_
    exact (hq.eq_of_le (Ideal.comap_ne_top _ (isMaximal_XYIdeal h'.1).ne_top)
      (span_X_sub_C_le_comap_XYIdeal W x (C y'))).ge
  have hmul : Ideal.relNorm F[X] (XYIdeal W.toAffine x (C (W.toAffine.negY x y))) *
      Ideal.relNorm F[X] (XYIdeal W.toAffine x (C y)) = Ideal.span {X - C x} ^ 2 := by
    rw [← map_mul, XYIdeal_neg_mul h, XIdeal_eq_map, Ideal.relNorm_algebraMap,
      finrank_coordinateRing]
  obtain ⟨a, ha⟩ := Ideal.dvd_iff_le.mpr (hle h)
  obtain ⟨b, hb⟩ := Ideal.dvd_iff_le.mpr (hle ((nonsingular_neg ..).mpr h))
  rw [ha, hb, pow_two] at hmul
  have hq0 : (Ideal.span {X - C x} : Ideal F[X]) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero x
  have hba : b * a = 1 := by
    refine mul_left_cancel₀ (mul_ne_zero hq0 hq0) ?_
    calc Ideal.span {X - C x} * Ideal.span {X - C x} * (b * a)
        = Ideal.span {X - C x} * b * (Ideal.span {X - C x} * a) := by ring
      _ = _ := hmul
      _ = _ := (mul_one _).symm
  have ha1 : a = 1 := by
    rw [Ideal.one_eq_top] at hba ⊢
    exact eq_top_iff.mpr (by rw [← hba, mul_comm]; exact Ideal.mul_le_left)
  rw [ha, ha1, mul_one]

omit [IsAlgClosed F] [W.IsElliptic] in
theorem finite_support_count [IsDedekindDomain W.toAffine.CoordinateRing]
    (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) :
    (Function.support fun v : HeightOneSpectrum W.toAffine.CoordinateRing =>
      FractionalIdeal.count W.toAffine.FunctionField v I).Finite :=
  Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)

theorem finsum_count_XYIdeal {x y : F} (h : W.toAffine.Nonsingular x y) :
    ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        ((XYIdeal W.toAffine x (C y) : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) = 1 := by
  classical
  have hc := fun v => FractionalIdeal.count_maximal W.toAffine.FunctionField v
    (heightOneOfNonsingular h)
  simp only [heightOneOfNonsingular_asIdeal] at hc
  rw [finsum_eq_single _ (heightOneOfNonsingular h) (fun v hv => by
    rw [hc v, if_neg (fun e => hv e.symm)]), hc, if_pos rfl]

theorem natDegree_eq_finsum_count_of_relNorm_eq {I : Ideal W.toAffine.CoordinateRing} (hI : I ≠ 0)
    {p : F[X]} (hp : Ideal.relNorm F[X] I = Ideal.span {p}) :
    (p.natDegree : ℤ) = ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        (I : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime generalizing p with
  | h₁ => exact absurd rfl hI
  | h₂ I hu =>
    rw [Ideal.isUnit_iff.mp hu, Ideal.relNorm_top, eq_comm, Ideal.span_singleton_eq_top] at hp
    rw [Ideal.isUnit_iff.mp hu, FractionalIdeal.coeIdeal_top]
    simp [FractionalIdeal.count_one, natDegree_eq_zero_of_isUnit hp]
  | h₃ a P ha hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have := Ideal.isPrime_of_prime hP
    obtain ⟨x, y, h, rfl⟩ := exists_eq_XYIdeal W hP0
    obtain ⟨g, hg⟩ : ∃ g, Ideal.relNorm F[X] a = Ideal.span {g} :=
      ⟨_, (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
    have hg0 : g ≠ 0 := by
      rintro rfl
      have hb : Ideal.relNorm F[X] a = ⊥ := by rw [hg]; simp
      exact ha (Ideal.relNorm_eq_bot_iff.mp hb)
    rw [map_mul, relNorm_XYIdeal W h, hg, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_span_singleton] at hp
    have hdeg : p.natDegree = ((X - C x) * g).natDegree :=
      natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hp).symm
    have hc0 : ((XYIdeal W.toAffine x (C y) : Ideal _) :
        FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hP0
    have ha0 : (a : FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr ha
    rw [hdeg, natDegree_mul (X_sub_C_ne_zero x) hg0, natDegree_X_sub_C,
      FractionalIdeal.coeIdeal_mul]
    simp_rw [FractionalIdeal.count_mul _ _ hc0 ha0]
    rw [finsum_add_distrib (finite_support_count W _) (finite_support_count W _),
      finsum_count_XYIdeal W h, ← ih ha hg]
    push_cast
    ring

theorem natDegree_norm_eq_finsum_count {f : W.toAffine.CoordinateRing} (hf : f ≠ 0) :
    ((Algebra.norm F[X] f).natDegree : ℤ) = ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        ((Ideal.span {f} : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by
  refine natDegree_eq_finsum_count_of_relNorm_eq W ?_ ?_
  · rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  · rw [Ideal.relNorm_singleton, Algebra.intNorm_eq_norm]

end GroundTheory.Arith.Abelian

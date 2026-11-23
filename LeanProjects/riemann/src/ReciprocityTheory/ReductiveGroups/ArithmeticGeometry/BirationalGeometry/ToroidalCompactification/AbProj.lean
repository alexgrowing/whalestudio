import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArcSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isProper_str (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  haveI : IsScalarTower R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hf : Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have hP : IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) := by
    infer_instance

  have hbij : Function.Bijective
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)) := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      exact MvPolynomial.C_injective _ _ this
    · rintro ⟨p, hp⟩
      rw [MvPolynomial.mem_homogeneousSubmodule] at hp
      have ht : p.totalDegree = 0 := Nat.le_zero.mp hp.totalDegree_le
      refine ⟨MvPolynomial.coeff 0 p, Subtype.ext ?_⟩
      exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp ht).symm
  haveI : IsIso (CommRingCat.ofHom
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  unfold PSpace.str
  infer_instance

theorem projProper : ProjProperSt := by
  intro R _ X f hf
  obtain ⟨N, i, hi, rfl⟩ := hf
  haveI := hi
  haveI := isProper_str R N
  infer_instance

theorem abLocusOne : AbLocusOneSt := by
  rintro S G _ hG K _ t ht s ⟨p, rfl⟩ K' _ _ t' ⟨p', hp'⟩
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := t') p p' hp'.symm
  let j := (pullback t t').fromSpecResidueField z
  let u := j ≫ pullback.fst t t'
  let u' := j ≫ pullback.snd t t'
  have e : u ≫ t = u' ≫ t' := by simp only [u, u', Category.assoc, pullback.condition]
  have P₁ := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have P₂ := (IsPullback.of_hasPullback (pullback.snd G.hom t') u').paste_horiz (IsPullback.of_hasPullback G.hom t')
  rw [← e] at P₂
  have h₂ : UniversallyClosed (pullback.snd (pullback.snd G.hom t') u') := by
    rw [← (P₂.isoIsPullback _ _ P₁).hom_inv_id_assoc (pullback.snd (pullback.snd G.hom t') u'),
      P₂.isoIsPullback_inv_snd]
    infer_instance
  have : Subsingleton (Sp K') := inferInstanceAs (Subsingleton (PrimeSpectrum K'))
  have hu' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u' :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t') :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu' h₂
  have := hG.separated
  have := hG.smooth
  exact ⟨⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

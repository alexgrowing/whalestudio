import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

namespace GlobalTheory.SmoothDescent

section Rings

open TensorProduct KaehlerDifferential

theorem flat_of_formallySmooth_of_essFiniteType (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Algebra.EssFiniteType R B] [Algebra.FormallySmooth R B] :
    Module.Flat R B := by
  let P := Algebra.EssFiniteType.subalgebra R B
  let M : Submonoid P := Algebra.EssFiniteType.submonoid R B
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R P)
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] B := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R P B).comp f₀) fun x ↦
    IsLocalization.map_units (M := M) B ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    exact (IsLocalization.lift_mk'_spec (M := M') (S := P')
      (g := ((IsScalarTower.toAlgHom R P B).comp f₀).toRingHom)
      (fun x ↦ IsLocalization.map_units (M := M) B ⟨f₀ x.1, x.2⟩) x _ ⟨s, hs⟩).mpr
      (IsLocalization.mk'_spec' B (f₀ x) (⟨f₀ s, hs⟩ : M)).symm
  have : Module.Flat R P' := .trans R (MvPolynomial (Fin n) R) P'
  exact Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing fP hf₁

theorem formallySmooth_of_flat_of_formallyUnramified (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    [Algebra.EssFiniteType R A] [Module.Flat R A] [Algebra.FormallyUnramified R A] :
    Algebra.FormallySmooth R A := by
  have : Algebra.FormallyEtale (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] A) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FinitePresentation R (Algebra.EssFiniteType.subalgebra R A) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (Algebra.EssFiniteType.submonoid R A)

theorem formallyEtale_of_bijective_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Algebra.FormallySmooth R B]
    (h : Function.Bijective (mapBaseChange R P B)) : Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

theorem formallySmooth_of_faithfullyFlat (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsNoetherianRing R] [IsLocalRing A]
    [Algebra.EssFiniteType R A] [Algebra.EssFiniteType A B] [Module.FaithfullyFlat A B]
    [Algebra.FormallyEtale A B] [Algebra.FormallySmooth R B] : Algebra.FormallySmooth R A := by
  classical
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing R A
  have : Algebra.EssFiniteType R B := .comp R A B
  have : Module.FinitePresentation A Ω[A⁄R] := Module.finitePresentation_of_finite _ _
  have : Module.Flat B (B ⊗[A] Ω[A⁄R]) := .of_linearEquiv (tensorKaehlerEquivOfFormallyEtale R A B)
  have : Module.Flat A Ω[A⁄R] := Module.Flat.of_flat_tensorProduct _ _ B
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _ (span_range_derivation R A)
  have : Finite κ := Module.Finite.finite_basis b
  let P := MvPolynomial κ R
  let φ : P →ₐ[R] A := MvPolynomial.aeval a
  algebraize [φ.toRingHom, (algebraMap A B).comp φ.toRingHom]
  have : IsScalarTower R P B := .to₁₂₄ R P A B
  have hX (i : κ) : algebraMap P A (MvPolynomial.X i) = a i := MvPolynomial.aeval_X _ _
  let bB : Module.Basis κ B Ω[B⁄R] := (b.baseChange B).map (tensorKaehlerEquivOfFormallyEtale R A B)
  let bP : Module.Basis κ B (B ⊗[P] Ω[P⁄R]) := (mvPolynomialBasis R κ).baseChange B
  have hbij : Function.Bijective (mapBaseChange R P B) := by
    have : mapBaseChange R P B = (bP.equiv bB (Equiv.refl κ)).toLinearMap := by
      refine bP.ext fun i => ?_
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      simp [bP, bB, hb, ← hX, ← IsScalarTower.algebraMap_apply, P]
    rw [this]
    exact (bP.equiv bB (Equiv.refl κ)).bijective
  have : Algebra.FormallyEtale P B := formallyEtale_of_bijective_mapBaseChange R P B hbij
  let p : Ideal P := (IsLocalRing.maximalIdeal A).comap (algebraMap P A)
  let Q := Localization.AtPrime p
  let ψ : Q →ₐ[P] A := IsLocalization.liftAlgHom (M := p.primeCompl) (f := Algebra.ofId P A) fun x => by
    by_contra h
    exact x.2 h
  algebraize [ψ.toRingHom, (algebraMap A B).comp ψ.toRingHom]
  have : IsScalarTower P Q B := .to₁₂₄ P Q A B
  have : IsScalarTower R Q A := .to₁₃₄ R P Q A
  have : IsScalarTower R Q B := .to₁₂₄ R Q A B
  have : IsLocalHom (algebraMap Q A) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff Q p]
    intro hxp
    have e : algebraMap P A x = algebraMap P A s * algebraMap Q A (IsLocalization.mk' Q x s) := by
      rw [IsScalarTower.algebraMap_apply P Q A s, ← map_mul, IsLocalization.mk'_spec',
        ← IsScalarTower.algebraMap_apply]
    have hs : IsUnit (algebraMap P A s) := by
      by_contra h
      exact s.2 h
    exact hxp (e ▸ hs.mul hx)
  have : Algebra.FormallyEtale Q B := Algebra.FormallyEtale.localization_base p.primeCompl
  have : Algebra.EssFiniteType Q A := .of_comp R Q A
  have : Algebra.EssFiniteType Q B := .of_comp R Q B
  have : Module.Flat Q B := flat_of_formallySmooth_of_essFiniteType Q B
  have : Module.Flat Q A := by
    rw [← RingHom.flat_algebraMap_iff]
    refine ringHom_flat_of_comp_faithfullyFlat (β := algebraMap A B)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) ?_
    rw [← IsScalarTower.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Algebra.FormallyUnramified Q A := by
    have h1 : Subsingleton (B ⊗[A] Ω[A⁄Q]) := (tensorKaehlerEquivOfFormallyEtale Q A B).subsingleton
    exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B).mp h1⟩
  have : Algebra.FormallySmooth Q A := formallySmooth_of_flat_of_formallyUnramified Q A
  have : Algebra.FormallySmooth P A := .comp P Q A
  exact .comp R P A

end Rings

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem smooth_of_comp_of_etale_of_surjective {X Y S : Scheme.{0}} (π : X ⟶ Y) (s : Y ⟶ S)
    [IsLocallyNoetherian S] [Etale π] [Surjective π] [LocallyOfFiniteType s] [Smooth (π ≫ s)] :
    Smooth s := by
  have : LocallyOfFinitePresentation s := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have : Flat π := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale π›).1
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := π.surjective y
  rw [Scheme.Hom.mem_smoothLocus]
  have h : ((π ≫ s).stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp ((π ≫ s).smoothLocus_eq_top.ge (Set.mem_univ x))
  rw [Scheme.Hom.stalkMap_comp] at h
  replace h : ((π.stalkMap x).hom.comp (s.stalkMap (π x)).hom).FormallySmooth := h
  have hs : (π.stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (π.smoothLocus_eq_top.ge (Set.mem_univ x))
  have hu := FormallyUnramified.stalkMap π x
  have hf := faithfullyFlat_stalkMap_of_flat π x
  have e₁ := LocallyOfFiniteType.stalkMap π x
  have e₂ := LocallyOfFiniteType.stalkMap s (π x)
  algebraize [(π.stalkMap x).hom, (s.stalkMap (π x)).hom, (π.stalkMap x).hom.comp (s.stalkMap (π x)).hom]
  have : Algebra.FormallyEtale (Y.presheaf.stalk (π x)) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  exact formallySmooth_of_faithfullyFlat (S.presheaf.stalk (s (π x))) (Y.presheaf.stalk (π x))
    (X.presheaf.stalk x)

theorem smoothOfRelativeDimension_of_etale_cover :
    ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  intro K _ X Y π s d _ _ _ hd
  have : Smooth (π ≫ s) := SmoothOfRelativeDimension.smooth d _
  have : Smooth s := smooth_of_comp_of_etale_of_surjective π s
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose n W hW hn using H1.exists_dim s
  have key (y : Y) : n y = d := by
    obtain ⟨x, rfl⟩ := π.surjective y
    have := hn (π x)
    have h₁ : SmoothOfRelativeDimension (0 + n (π x)) ((π ∣_ W (π x)) ≫ (W (π x)).ι ≫ s) := inferInstance
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
    have h₂ : SmoothOfRelativeDimension (0 + d) ((π ⁻¹ᵁ W (π x)).ι ≫ π ≫ s) := inferInstance
    simpa using H1.dim_unique _ h₁ h₂ ⟨x, hW (π x)⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W ?_ fun y => key y ▸ hn y
  rw [← top_le_iff]
  rintro y -
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩

end GlobalTheory.SmoothDescent

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GenericEtale

theorem trdeg_eq (k K A B : Type) [CommRing k] [IsDomain k] [Field K] [Algebra k K]
    [IsFractionRing k K] [CommRing A] [Algebra k A] [FaithfulSMul k A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsAlgebraic A B] [Algebra K B] [Algebra k B]
    [IsScalarTower k K B] [IsScalarTower k A B] : Algebra.trdeg K B = Algebra.trdeg k A := by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  have : Algebra.IsAlgebraic k K := IsLocalization.isAlgebraic K (nonZeroDivisors k)
  have h₁ := trdeg_add_eq k K (A := B)
  have h₂ := trdeg_add_eq k A (A := B)
  rw [trdeg_eq_zero, zero_add] at h₁
  rw [trdeg_eq_zero (R := A), add_zero] at h₂
  rw [h₁, h₂]

theorem formallySmooth_fractionField (k A L : Type) [CommRing k] [IsDomain k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [FaithfulSMul k A] [Algebra.FiniteType k A] [Field L]
    [Algebra A L] [IsFractionRing A L] [Algebra k L] [IsScalarTower k A L] :
    Algebra.FormallySmooth k L ∧ Module.rank L Ω[L⁄k] = Algebra.trdeg k A := by
  let K := FractionRing k
  have hinj : Function.Injective (algebraMap k L) := by
    rw [IsScalarTower.algebraMap_eq k A L]
    exact (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective k A)
  let : Algebra K L := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := K) hinj a).symm
  have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
  have : Algebra.EssFiniteType k L := .comp k A L
  have : Algebra.EssFiniteType K L := .of_comp k K L
  have : Algebra.FormallySmooth K L := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallyEtale k K := .of_isLocalization (nonZeroDivisors k)
  have : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  refine ⟨.comp k K L, ?_⟩
  have hb : Function.Bijective (KaehlerDifferential.map k K L L) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, KaehlerDifferential.map_surjective k K L⟩
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map k K L x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  rw [(LinearEquiv.ofBijective _ hb).rank_eq, rank_kaehler_eq_trdeg, trdeg_eq k K A L]

theorem exists_away (k A : Type) [CommRing k] [IsDomain k] [CharZero k] [IsNoetherianRing k]
    [CommRing A] [IsDomain A] [Algebra k A] [FaithfulSMul k A] [Algebra.FiniteType k A] {D : ℕ}
    (hd : Algebra.trdeg k A = D) :
    ∃ f : A, f ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension D k (Localization.Away f) := by
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let L := Localization.AtPrime (⊥ : Ideal A)
  have : IsFractionRing A L :=
    (congrArg (fun M : Submonoid A => IsLocalization M L) (Ideal.primeCompl_bot (α := A))).mp
      inferInstance
  have hL : IsField L :=
    (FractionRing.algEquiv A L).symm.toMulEquiv.isField (Field.toIsField (FractionRing A))
  let : Field L := hL.toField
  obtain ⟨h₁, h₂⟩ := formallySmooth_fractionField k A L
  have : Algebra.IsSmoothAt k (⊥ : Ideal A) := h₁
  obtain ⟨f, hf, h⟩ := exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k (⊥ : Ideal A)
    (d := D) (Module.finrank_eq_of_rank_eq (h₂.trans hd))
  exact ⟨f, hf, h⟩

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem trdeg_chart (h : IsArithVar p D) {A : Type} [CommRing A] [Algebra k A]
    (i : Sp A ⟶ X) [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    Algebra.trdeg k A = D := by
  have := h.isDomain
  let K := FractionRing k
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨_, hd⟩ := RegGenSmooth.ringKrullDim_chart h
    (IsPullback.of_hasPullback p (spMap (algebraMap k K))) i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : FaithfulSMul A (K ⊗[k] A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic A (K ⊗[k] A) :=
    IsLocalization.isAlgebraic _ (Algebra.algebraMapSubmonoid A (nonZeroDivisors k))
  obtain ⟨d, hd₁, hd₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq K (K ⊗[k] A)
  have e : d = D := by exact_mod_cast hd₁.symm.trans hd
  rw [← trdeg_eq k K A (K ⊗[k] A), hd₂, e]

theorem exists_etale_coords [IsIntegral X] (h : IsArithVar p D) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  have := h.isDomain
  have := h.charZero_base
  have := h.isNoetherianRing
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨f, hf, hs⟩ := exists_away k A (trdeg_chart h i hi)
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization f
  let j : Sp B ⟶ X := spMap (algebraMap A B) ≫ i
  have hj : j ≫ p = spMap (algebraMap k B) := by
    rw [Category.assoc, hi, IsScalarTower.algebraMap_eq k A B, ← Spec.map_comp]
    rfl
  have h₁ : SmoothOfRelativeDimension D (j ≫ p) := by
    rw [hj]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension D)).mpr ?_
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).mpr hs)
  have h₂ : SmoothOfRelativeDimension D (j.opensRange.ι ≫ p) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    have : SmoothOfRelativeDimension (0 + D) (j.isoOpensRange.inv ≫ j ≫ p) := inferInstance
    rwa [zero_add] at this
  refine ModelCharts.exists_etale_coords_of_opens p D j.opensRange ?_
  exact ⟨genericPoint _, genericPoint_eq_of_isOpenImmersion j⟩

theorem exists_etale_coord_surface : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X], IsArithVar p 1 → ∃ (U : X.Opens) (x : Fin 1 → Γ(X, U)), IsAffineOpen U ∧
      genericPoint X ∈ U ∧ (MvPolynomial.eval₂Hom (algX p U) x).Etale :=
  fun _ _ _ _ _ h => exists_etale_coords h

end GlobalTheory.GenericEtale

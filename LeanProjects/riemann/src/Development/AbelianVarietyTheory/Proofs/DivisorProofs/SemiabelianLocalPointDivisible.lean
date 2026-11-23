import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleExtensionUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianMulNatSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatQuasiSectionStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.Divis

theorem nonempty_section : ∀ (S K A : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Field K] [IsAlgClosed K]
    [Algebra S K] [IsFractionRing S K] [CommRing A] [Algebra S A], Module.Finite S A → Module.Flat S A → Nontrivial A →
    Nonempty (A →ₐ[S] S) := by
  intro S K A _ _ _ _ _ _ _ _ _ hfin hfl hnt
  haveI : Algebra.IsIntegral S A := Algebra.IsIntegral.of_finite S A
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  have hj : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[S] K ⊗[S] A) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S K)
  obtain ⟨σ, -⟩ := GlobalTheory.GroupBplus.Rigid.exists_section (K := K) (Algebra.TensorProduct.includeRight : A →ₐ[S] K ⊗[S] A) hj M
  exact ⟨σ⟩

theorem exists_pow_eq : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (q : PrimeSpectrum R) (x : SpAlg R (Localization.AtPrime q.asIdeal) ⟶ G) (m : ℕ), m ≠ 0 → ∃ y, y ^ m = x := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG q x m hm
  let Rq := Localization.AtPrime q.asIdeal
  letI : Algebra Rq K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ K q.asIdeal.primeCompl (nonZeroDivisors R) q.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower R Rq K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ K q.asIdeal.primeCompl (nonZeroDivisors R)
      q.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Rq K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl _ K
  haveI : IsIntegrallyClosed Rq :=
    isIntegrallyClosed_of_isLocalization _ q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : HenselianLocalRing Rq := henselianLocalRing_atPrime R K q.asIdeal
  have hfq := GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ G hG m hm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  let ml := ((𝟙 G) ^ m : G ⟶ G).left
  have hml : ml ≫ G.hom = G.hom := Over.w _
  haveI : Flat ml := hfq.1
  haveI : LocallyQuasiFinite ml := hfq.2
  haveI : IsSeparated ml := by
    have : IsSeparated (ml ≫ G.hom) := by rw [hml]; infer_instance
    exact IsSeparated.of_comp ml G.hom
  haveI : LocallyOfFiniteType ml := by
    have : LocallyOfFiniteType (ml ≫ G.hom) := by rw [hml]; infer_instance
    exact locallyOfFiniteType_of_comp ml G.hom
  haveI : QuasiCompact ml := by
    have : QuasiCompact (ml ≫ G.hom) := by rw [hml]; infer_instance
    exact QuasiCompact.of_comp ml G.hom
  let f := pullback.snd ml x.left
  haveI := GlobalTheory.T.semiAbelian_mul_nat_surjective _ G hG m hm
  obtain ⟨g, hg⟩ := ml.surjective (x.left (IsLocalRing.closedPoint Rq))
  obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback ml x.left) g
    (IsLocalRing.closedPoint Rq) hg
  obtain ⟨A, _, _, hfin, hfl, hnt, h, hh⟩ := GlobalTheory.T.exists_finite_flat_quasi_section Rq _ f ⟨y, hy⟩
  obtain ⟨σ⟩ := nonempty_section Rq K A hfin hfl hnt
  let s : Sp Rq ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (σ : A →+* Rq))
  have hs : s ≫ h ≫ f = 𝟙 _ := by
    rw [hh, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact σ.commutes a
  let yl : Sp Rq ⟶ G.left := s ≫ h ≫ pullback.fst ml x.left
  have hyl : yl ≫ ml = x.left := by
    have e : yl ≫ ml = (s ≫ h ≫ f) ≫ x.left := by
      simp only [yl, f, Category.assoc, pullback.condition]
    rw [e, hs, Category.id_comp]
  have e' (z : SpAlg R Rq ⟶ G) : z ^ m = z ≫ (𝟙 G) ^ m := by rw [MonObj.comp_pow, Category.comp_id]
  refine ⟨Over.homMk yl (by rw [← hml, ← Category.assoc, hyl]; exact Over.w x), ?_⟩
  rw [e']
  exact Over.OverMorphism.ext hyl

end GlobalTheory.GroupBplus.Aff.Divis

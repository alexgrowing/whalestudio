import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem spMap_fst_surjective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : Function.Surjective (spMap (TrivSqZeroExt.fstHom R R M).toRingHom) := by
  intro q
  haveI : q.asIdeal.IsPrime := q.2
  refine ⟨⟨q.asIdeal.comap (TrivSqZeroExt.inlHom R M), Ideal.IsPrime.comap _⟩, ?_⟩
  apply PrimeSpectrum.ext
  ext a
  show (TrivSqZeroExt.inlHom R M) ((TrivSqZeroExt.fstHom R R M) a) ∈ q.asIdeal ↔ a ∈ q.asIdeal
  have hm : TrivSqZeroExt.inr a.snd ∈ q.asIdeal :=
    q.2.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact q.asIdeal.zero_mem)
  have e : TrivSqZeroExt.inl a.fst + TrivSqZeroExt.inr a.snd = a := TrivSqZeroExt.inl_fst_add_inr_snd_eq a
  constructor
  · intro h
    rw [← e]
    exact q.asIdeal.add_mem h hm
  · intro h
    show TrivSqZeroExt.inl a.fst ∈ q.asIdeal
    rw [eq_sub_of_add_eq e]
    exact q.asIdeal.sub_mem h hm

theorem exists_basicOpen_inl {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] {X : Scheme.{0}} (x : Sp R ⟶ X) (q : Sp (TrivSqZeroExt R M)) :
    ∃ (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (U : X.affineOpens), q ∈ (Sp (TrivSqZeroExt R M)).basicOpen s ∧
      spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s ≤ x ⁻¹ᵁ U.1 := by
  obtain ⟨q₀, rfl⟩ := spMap_fst_surjective R M q
  obtain ⟨U, hUa, hU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x q₀ ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show q₀ ∈ ((x ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) from hU) (x ⁻¹ᵁ U).2
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv (TrivSqZeroExt.inl r), ⟨U, hUa⟩, ?_, ?_⟩
  · rw [AlgebraicGeometry.basicOpen_eq_of_affine]
    exact hr
  · intro w hw
    rw [Scheme.Hom.mem_preimage, AlgebraicGeometry.basicOpen_eq_of_affine] at hw
    exact hle hw

end GlobalTheory.Pinch

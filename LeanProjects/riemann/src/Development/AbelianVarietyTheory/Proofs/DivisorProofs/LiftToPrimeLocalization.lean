import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory

theorem spec_factor_localization_of_field_point : ∀ (U X : Scheme.{0}) (j : U ⟶ X) [IsOpenImmersion j] (R : Type) [CommRing R] (ξ : Sp R ⟶ X)
    (K' : Type) [Field K'] (χ : R →+* K') (yy : Sp K' ⟶ U), spMap χ ≫ ξ = yy ≫ j →
    ∀ (q : Ideal R) [q.IsPrime], RingHom.ker χ = q →
      ∃ yq : Sp (Localization.AtPrime q) ⟶ U, spMap (algebraMap R (Localization.AtPrime q)) ≫ ξ = yq ≫ j := by
  intro U X j _ R _ ξ K' _ χ yy h q _ hq
  have hopen : IsOpen (Set.range j) := j.isOpenEmbedding.isOpen_range
  let pt : Sp K' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K')
  have hpt : (spMap χ pt : PrimeSpectrum R) = (⟨q, inferInstance⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    change Ideal.comap χ ⊥ = q
    rw [← hq]; rfl
  have hmem : ξ (⟨q, inferInstance⟩ : PrimeSpectrum R) ∈ Set.range j := by
    refine ⟨yy pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
    exact congrArg ξ hpt
  refine ⟨IsOpenImmersion.lift j (spMap (algebraMap R (Localization.AtPrime q)) ≫ ξ) ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have hle : (spMap (algebraMap R (Localization.AtPrime q)) x : PrimeSpectrum R) ⤳
        (⟨q, inferInstance⟩ : PrimeSpectrum R) := by
      have hle' : Ideal.comap (algebraMap R (Localization.AtPrime q)) (x : PrimeSpectrum _).asIdeal ≤ q := by
        intro r hr
        by_contra hrq
        have hu : IsUnit (algebraMap R (Localization.AtPrime q) r) :=
          IsLocalization.map_units (Localization.AtPrime q) (⟨r, hrq⟩ : q.primeCompl)
        exact (x : PrimeSpectrum _).isPrime.ne_top ((Ideal.eq_top_of_isUnit_mem _ hr hu))
      exact (PrimeSpectrum.le_iff_specializes
        (spMap (algebraMap R (Localization.AtPrime q)) x : PrimeSpectrum R) ⟨q, inferInstance⟩).1 hle'
    exact (hle.map ξ.continuous).mem_open hopen hmem
  · exact (IsOpenImmersion.lift_fac _ _ _).symm

end GlobalTheory

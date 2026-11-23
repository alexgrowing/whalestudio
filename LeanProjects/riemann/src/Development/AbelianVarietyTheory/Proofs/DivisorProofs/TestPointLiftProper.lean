import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper

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
namespace GlobalTheory.FlatModel

theorem field_pt_eq_bot {K : Type} [Field K] (z : Sp K) : z = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) :=
  by haveI := z.isPrime; exact PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)

theorem isTest_lift (p : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X) (hπ : IsProper π) (Xw O : X.Opens)
    (hO : Xw ≤ O) (hiso : IsIso (π ∣_ O)) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (hyb : IsTest p Xw yb) :
    ∃ yb', IsTest p (π ⁻¹ᵁ Xw) yb' ∧ yb' ≫ π = yb := by
  obtain ⟨⟨T, kO, yT, hfin, hinj, hyT⟩, hrange⟩ := hyb
  have hgen : yT (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ Xw := by
    have h1 := hrange ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p]), rfl⟩
    rw [bot_map (FaithfulSMul.algebraMap_injective 𝓞_ℂ_[p] ℂ_[p]), ← hyT, bot_map hinj] at h1
    exact h1
  set y : Sp T.Fr ⟶ X := spMap (algebraMap T.V T.Fr) ≫ yT with hy
  have hyO : Set.range y ⊆ (O : Set X) := by
    rintro _ ⟨z, rfl⟩
    rw [field_pt_eq_bot z, hy, bot_map (IsFractionRing.injective T.V T.Fr)]
    exact hO hgen
  have hr : Set.range y ⊆ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hyO
  let y₀ : Sp T.Fr ⟶ O := IsOpenImmersion.lift O.ι y hr
  let y' : Sp T.Fr ⟶ X' := y₀ ≫ inv (π ∣_ O) ≫ (π ⁻¹ᵁ O).ι
  have hy' : y' ≫ π = spMap (algebraMap T.V T.Fr) ≫ yT := by
    simp only [y', Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, y₀, IsOpenImmersion.lift_fac]
    exact hy
  haveI : ValuationRing T.V := inferInstance
  obtain ⟨yT', -, hyT'⟩ := valuative_lift_of_isProper π y' yT hy'
  refine ⟨spMap kO ≫ yT', ⟨⟨T, kO, yT', hfin, hinj, rfl⟩, ?_⟩, by rw [Category.assoc, hyT', hyT]⟩
  rintro _ ⟨z, rfl⟩
  show π _ ∈ Xw
  have := hrange ⟨z, rfl⟩
  rw [← hyT, ← hyT'] at this
  simp only [Scheme.Hom.comp_apply, Category.assoc] at this
  exact this

end GlobalTheory.FlatModel

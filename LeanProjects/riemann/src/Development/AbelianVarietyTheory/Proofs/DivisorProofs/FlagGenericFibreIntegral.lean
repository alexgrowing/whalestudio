import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
open CategoryTheory.Limits
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlagGenFib

theorem isIntegral_of_flat_preimmersion {G X : Scheme.{0}} [IsIntegral X] (j : G ⟶ X) [Flat j]
    [IsPreimmersion j] (h : genericPoint X ∈ Set.range j) : IsIntegral G := by
  obtain ⟨g, hg⟩ := h
  have hcl : closure {g} = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    rw [← specializes_iff_mem_closure, ← j.isEmbedding.isInducing.specializes_iff, hg]
    exact genericPoint_specializes _
  have : IrreducibleSpace G :=
    (irreducibleSpace_def _).2 (show IsIrreducible (Set.univ : Set G) from
      hcl ▸ isIrreducible_singleton.closure)
  have : ∀ x : G, _root_.IsReduced (G.presheaf.stalk x) := fun x => by
    have hs := j.stalkMap_surjective x
    have hf := Flat.stalkMap j x
    have hi : Function.Injective (j.stalkMap x).hom := by
      let := (j.stalkMap x).hom.toAlgebra
      have : Module.Flat (X.presheaf.stalk (j x)) (G.presheaf.stalk x) := hf
      have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (G.presheaf.stalk x)) :=
        inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
      have : Module.FaithfullyFlat (X.presheaf.stalk (j x)) (G.presheaf.stalk x) :=
        Module.FaithfullyFlat.of_flat_of_isLocalHom
      exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (G.presheaf.stalk x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm
      (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm.injective
  have : IsReduced G := isReduced_of_isReduced_stalk G
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem asIdeal_genericPoint_eq_bot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {n : ℕ} (hX : IsArithVar p n) : (p (genericPoint X)).asIdeal = ⊥ := by
  have := hX.isDomain
  have := hX.finite
  have := hX.flat
  let t := p ≫ spMap (Int.castRingHom k)
  have hb : (show Sp ℤ from (⊥ : PrimeSpectrum ℤ)) ⤳ t (genericPoint X) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨z, hz, hz'⟩ := Flat.generalizingMap t hb
  obtain rfl : z = genericPoint X := (hz.antisymm (genericPoint_specializes z)).eq
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  exact congrArg PrimeSpectrum.asIdeal hz'

theorem isIntegral_Gf : ∀ {D : D7} {Bs Y₀ : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (π₀ : Y₀ ⟶ Bs) (n : ℕ),
    IsArithVar (π₀ ≫ q) n → IsIntegral (GlobalTheory.FlagGenFib.Gf q π₀) := by
  intro D Bs Y₀ q π₀ n h
  have := h.isIntegral
  have : IsPreimmersion (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 D.what₂.LL)) (S := D.what₂.LL)
  have : Flat (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors (𝓞 D.what₂.LL)))
  have : IsPreimmersion (jf q π₀) := by unfold jf Gf; infer_instance
  have : Flat (jf q π₀) := by unfold jf Gf; infer_instance
  refine isIntegral_of_flat_preimmersion (jf q π₀) ?_
  have hr := Scheme.Pullback.range_fst (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))
  refine hr.ge ⟨(⊥ : PrimeSpectrum D.what₂.LL), PrimeSpectrum.ext ?_⟩
  rw [asIdeal_genericPoint_eq_bot h]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)

end GlobalTheory.FlagGenFib

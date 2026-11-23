import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GModStalk

theorem charZero_essFiniteType_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X),
    CharZero (Z.X.presheaf.stalk z) ∧ Algebra.EssFiniteType ℤ (Z.X.presheaf.stalk z) := by
  intro E _ _ _ H D l Xo c Z z
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨-, hft, -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  haveI : Flat Z.s := Z.flat
  let y : PrimeSpectrum (𝓞 c.F) := Z.s z
  letI : Algebra (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z))
  have h₁ : (Z.s.stalkMap z).hom.EssFiniteType := LocallyOfFiniteType.stalkMap Z.s z
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have hσ : Function.Injective (Z.s.stalkMap z).hom := by
    have h := Flat.stalkMap Z.s z
    algebraize [(Z.s.stalkMap z).hom]
    have : IsLocalHom (algebraMap ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z)) :=
      Z.s.toLRSHom.prop z
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp (𝓞 c.F)).presheaf.stalk (Z.s z))
      (B := Z.X.presheaf.stalk z)
    exact FaithfulSMul.algebraMap_injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z)
  refine ⟨charZero_of_injective_ringHom (f := (Z.s.stalkMap z).hom.comp φ) (hσ.comp hφ), ?_⟩
  have hO : Algebra.EssFiniteType ℤ (𝓞 c.F) := inferInstance
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hO).comp (h₂.comp h₁) using 1
  exact Subsingleton.elim _ _

end GlobalTheory.GModStalk

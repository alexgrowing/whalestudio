import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegDataIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinLift

theorem lift_point_finite_surjective : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (y : Sp K ⟶ X) (q : Y ⟶ X), IsFinite q → Surjective q → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (y' : Sp L ⟶ Y), y' ≫ q = spMap (algebraMap K L) ≫ y := by
  intro K _ X Y y q hq hs
  haveI := hq
  haveI := hs
  have : IsAffine (pullback q y) := isAffine_of_isAffineHom (pullback.snd q y)
  let e := (pullback q y).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ pullback.snd q y)
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  obtain ⟨p, -⟩ := (pullback.snd q y).surjective x
  let pt : PrimeSpectrum Γ(pullback q y, ⊤) := e.hom.base p
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal pt.asIdeal pt.isPrime.ne_top
  let L := Γ(pullback q y, ⊤) ⧸ m
  letI : Field L := Ideal.Quotient.field m
  let ψ : K →+* L := (Ideal.Quotient.mk m).comp φ.hom
  letI : Algebra K L := ψ.toAlgebra
  have hψ : ψ.Finite := RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hfin
  haveI : FiniteDimensional K L := hψ
  refine ⟨L, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ e.inv ≫ pullback.fst q y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv, ← hφ,
    ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.FinLift

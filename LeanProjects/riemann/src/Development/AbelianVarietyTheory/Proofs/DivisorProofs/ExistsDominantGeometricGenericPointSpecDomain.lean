import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

theorem exists_geomGeneric_dominant : ∀ (A : CommRingCat.{0}) [IsDomain A], ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ Spec A), (∀ x, (y x).asIdeal = ⊥) ∧ IsDominant y := by
  intro A _
  let Ω := AlgebraicClosure (FractionRing A)
  let φ : A →+* Ω := algebraMap A Ω
  have hφ : Function.Injective φ := by
    have h1 : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A _
    have h2 : Function.Injective (algebraMap (FractionRing A) Ω) := (algebraMap (FractionRing A) Ω).injective
    have : φ = (algebraMap (FractionRing A) Ω).comp (algebraMap A (FractionRing A)) :=
      IsScalarTower.algebraMap_eq A (FractionRing A) Ω
    rw [this]; exact h2.comp h1
  refine ⟨Ω, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · intro x
    show Ideal.comap φ x.asIdeal = ⊥
    rw [show x.asIdeal = ⊥ from @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime x)]
    exact Ideal.comap_bot_of_injective _ hφ
  · rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le

end GlobalTheory

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem lift_mem_valuationSubring_iff {K L : Type*} [Field K] [Field L] (A : ValuationSubring L) (i : K →+* L)
    (h : Function.Injective (i.comp (A.comap i).subtype)) (x : FractionRing (A.comap i)) :
    IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h x ∈ A ↔
      x ∈ Set.range (algebraMap (A.comap i) (FractionRing (A.comap i))) := by
  let f := FractionRing.algEquiv (A.comap i) K
  have hf : IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h =
      i.comp f.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (A.comap i)) (RingHom.ext fun a => ?_)
    refine (IsFractionRing.lift_algebraMap h a).trans ?_
    exact congrArg i (f.commutes a).symm
  rw [hf]
  refine ⟨fun hx => ⟨⟨f x, hx⟩, f.injective (f.commutes _)⟩, ?_⟩
  rintro ⟨v, rfl⟩
  rw [← hf, IsFractionRing.lift_algebraMap]
  exact v.2

theorem intRing_complete_dvr : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → IsDiscreteValuationRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ ∀ x : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K), ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K))) := by
  intro p _ K hK
  have hmem : ∀ x : K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := fun x => mem_OO_iff _
  let e : integralClosure ℤ_[p] K ≃+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K :=
    { toFun := fun x => ⟨x.1, (hmem _).2 ((mem_integralClosure_padicInt_iff K _).1 x.2)⟩
      invFun := fun x => ⟨x.1, (mem_integralClosure_padicInt_iff K _).2 ((hmem _).1 x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] (integralClosure ℤ_[p] K)
  refine ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, fun x => ?_⟩
  · have := (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal _) e).2 hc
    rwa [IsLocalRing.map_ringEquiv_maximalIdeal] at this
  · rw [← mem_OO_iff]
    exact lift_mem_valuationSubring_iff (OO p) (algebraMap K (PadicAlgCl p))
      (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) x

end GlobalTheory

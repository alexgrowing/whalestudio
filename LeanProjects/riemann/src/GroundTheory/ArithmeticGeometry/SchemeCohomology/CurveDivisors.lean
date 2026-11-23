import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurvePlaces
import GroundTheory.FunctionField.Divisor
set_option maxSynthPendingDepth 1

open CategoryTheory AlgebraicGeometry Order Topology Module

open scoped WithZero

universe u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormalScheme X]

namespace PrimeDivisor

omit [IsLocallyNoetherian X] [IsNormalScheme X] in
lemma algebraMap_stalk_injective (x : X) :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
  IsFractionRing.injective _ _

noncomputable def stalkAlgEquiv (Z : PrimeDivisor X) :
    X.presheaf.stalk Z.point ≃ₐ[k] (Z.toPlace (k := k)).ring :=
  AlgEquiv.ofBijective
    { toRingHom := (Z.stalkToPlaceRing (k := k)).hom
      commutes' := fun c => by
        apply Subtype.val_injective
        change algebraMap (X.presheaf.stalk Z.point) X.functionField
          (algebraMap k (X.presheaf.stalk Z.point) c) = algebraMap k X.functionField c
        rw [← IsScalarTower.algebraMap_apply] }
    ⟨fun a b h => algebraMap_stalk_injective Z.point (congrArg Subtype.val h), fun r => by
      obtain ⟨a, ha⟩ := (Z.valuation_le_one_iff r).mp ((Z.mem_toPlace_ring r).mp r.2)
      exact ⟨a, Subtype.val_injective ha⟩⟩

noncomputable def degree (Z : PrimeDivisor X) : ℕ :=
  finrank k (IsLocalRing.ResidueField (X.presheaf.stalk Z.point))

end PrimeDivisor

noncomputable def WeilDivisor.degree : WeilDivisor X →+ ℤ :=
  Finsupp.liftAddHom fun Z => AddMonoidHom.mulRight ((Z.degree (k := k) : ℕ) : ℤ)

variable [IsProper (X ↘ Spec (.of k))]

noncomputable def divisorEquiv (hX : topologicalKrullDim X ≤ 1) :
    WeilDivisor X ≃+ Divisor k X.functionField :=
  Finsupp.domCongr (placeEquiv hX)

@[simp]
lemma divisorEquiv_apply_toPlace (hX : topologicalKrullDim X ≤ 1) (D : WeilDivisor X)
    (Z : PrimeDivisor X) : divisorEquiv (k := k) hX D Z.toPlace = D Z := by
  change Finsupp.equivMapDomain (placeEquiv hX) D (placeEquiv (k := k) hX Z) = D Z
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

variable [IsFunctionField k X.functionField]

theorem mem_L_divisorEquiv (hX : topologicalKrullDim X ≤ 1) (D : WeilDivisor X)
    (f : X.functionField) :
    f ∈ Divisor.L (divisorEquiv (k := k) hX D) ↔
      ∀ Z : PrimeDivisor X, Z.valuation f ≤ WithZero.exp (D Z) := by
  rw [Divisor.mem_L]
  constructor
  · intro h Z
    have := h Z.toPlace
    rwa [PrimeDivisor.toPlace_valuation, divisorEquiv_apply_toPlace] at this
  · intro h v
    obtain ⟨Z, rfl⟩ := PrimeDivisor.toPlace_surjective (k := k) hX v
    rw [PrimeDivisor.toPlace_valuation, divisorEquiv_apply_toPlace]
    exact h Z

end GroundTheory.Arith.SchemeCoh

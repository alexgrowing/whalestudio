import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.QuotEqZeroOfNotPrimeDivisor
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveDivisors
import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Module

universe w' u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsNoetherian X] [IsNormalScheme X] [IsProper (X ↘ Spec (.of k))]
  [IsFunctionField k X.functionField] (hX : topologicalKrullDim X ≤ 1)

noncomputable def toRepartition (a : repartitions k X) : Repartition k X.functionField :=
  Repartition.mk (fun v => a.1 ((placeEquiv (k := k) hX).symm v)) (by
    refine (a.2.image (placeEquiv (k := k) hX)).subset fun v hv => ?_
    refine ⟨(placeEquiv (k := k) hX).symm v, ?_, Equiv.apply_symm_apply _ _⟩
    intro h
    apply hv
    obtain ⟨Z, rfl⟩ := (placeEquiv (k := k) hX).surjective v
    rw [Equiv.symm_apply_apply] at h ⊢
    exact (Z.mem_toPlace_ring _).mpr h)

omit [IsFunctionField k X.functionField] in
lemma toRepartition_apply_toPlace (a : repartitions k X) (Z : PrimeDivisor X) :
    toRepartition (k := k) hX a Z.toPlace = a.1 Z := by
  rw [toRepartition, Repartition.mk_apply, ← placeEquiv_apply hX, Equiv.symm_apply_apply]

noncomputable def repartitionEquiv : repartitions k X ≃ₗ[k] Repartition k X.functionField where
  toFun := toRepartition hX
  invFun b := ⟨fun Z => b Z.toPlace, by
    refine ((Repartition.finite_not_mem b).preimage
      (PrimeDivisor.toPlace_injective (k := k)).injOn).subset fun Z hZ => ?_
    intro h
    exact hZ ((Z.mem_toPlace_ring _).mp h)⟩
  map_add' a b := Repartition.ext fun v => by
    simp only [toRepartition, Repartition.mk_apply, Repartition.add_apply]
    rfl
  map_smul' c a := Repartition.ext fun v => by
    simp only [toRepartition, Repartition.mk_apply, Repartition.smul_apply, RingHom.id_apply]
    change c • a.1 _ = _
    rw [Algebra.smul_def]
  left_inv a := Subtype.ext (funext fun Z => toRepartition_apply_toPlace hX a Z)
  right_inv b := Repartition.ext fun v => by
    obtain ⟨Z, rfl⟩ := PrimeDivisor.toPlace_surjective (k := k) hX v
    exact toRepartition_apply_toPlace hX _ Z

lemma map_boundedRepartitions (D : WeilDivisor X) :
    (boundedRepartitions k D).map (repartitionEquiv (k := k) hX).toLinearMap =
      Divisor.A (divisorEquiv (k := k) hX D) := by
  ext b
  rw [Submodule.mem_map_equiv, mem_boundedRepartitions, Divisor.mem_A]
  constructor
  · intro h v
    obtain ⟨Z, rfl⟩ := PrimeDivisor.toPlace_surjective (k := k) hX v
    have := (Z.mem_divisorSubgroup D _).mp (h Z)
    rw [PrimeDivisor.toPlace_valuation, divisorEquiv_apply_toPlace]
    exact this
  · intro h Z
    rw [PrimeDivisor.mem_divisorSubgroup]
    have := h Z.toPlace
    rwa [PrimeDivisor.toPlace_valuation, divisorEquiv_apply_toPlace] at this

lemma map_range_diagRepartition :
    (LinearMap.range (diagRepartition k X)).map (repartitionEquiv (k := k) hX).toLinearMap =
      Repartition.principal k X.functionField := by
  rw [← LinearMap.range_comp]
  congr 1

noncomputable def repartitionQuotientEquiv (D : WeilDivisor X) :
    (repartitions k X ⧸ (boundedRepartitions k D ⊔ LinearMap.range (diagRepartition k X))) ≃ₗ[k]
      (Repartition k X.functionField ⧸
        (Divisor.A (divisorEquiv (k := k) hX D) ⊔ Repartition.principal k X.functionField)) :=
  Submodule.Quotient.equiv _ _ (repartitionEquiv (k := k) hX) (by
    rw [Submodule.map_sup, map_boundedRepartitions, map_range_diagRepartition])

lemma globalL_eq (D : WeilDivisor X) :
    globalL k D = Divisor.L (divisorEquiv (k := k) hX D) := by
  ext f
  rw [mem_globalL, mem_L_divisorEquiv]

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

noncomputable def divisorH0EquivL (D : WeilDivisor X) :
    Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 0 ≃ₗ[k] Divisor.L (divisorEquiv (k := k) hX D) :=
  (divisorH0Equiv k D).trans (LinearEquiv.ofEq _ _ (globalL_eq hX D))

noncomputable def divisorH1EquivAdelic (D : WeilDivisor X) :
    Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 ≃ₗ[k]
      (Repartition k X.functionField ⧸
        (Divisor.A (divisorEquiv (k := k) hX D) ⊔ Repartition.principal k X.functionField)) :=
  (divisorH1Equiv k hX D).trans (repartitionQuotientEquiv hX D)

end GroundTheory.Arith.SchemeCoh

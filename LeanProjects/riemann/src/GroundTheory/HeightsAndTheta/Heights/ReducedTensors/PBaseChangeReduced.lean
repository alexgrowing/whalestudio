import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ReducedTensors.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

namespace SectionsLattice

namespace BaseChangeReduced

theorem isReduced_tensor_of_forall_isMaximal {k R B : Type} [Field k] [CommRing R] [Algebra k R]
    [IsJacobsonRing R] [IsReduced R] [CommRing B] [Algebra k B]
    (h : ∀ m : Ideal R, m.IsMaximal → IsReduced ((R ⧸ m) ⊗[k] B)) : IsReduced (R ⊗[k] B) := by
  let b := Module.Free.chooseBasis k B
  have key : ∀ (m : Ideal R) (i) (y : R ⊗[k] B),
      Ideal.Quotient.mk m ((Algebra.TensorProduct.basis R b).repr y i) =
        (Algebra.TensorProduct.basis (R ⧸ m) b).repr
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k m) (AlgHom.id k B) y) i := by
    intro m i y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a z => simp [Algebra.TensorProduct.basis_repr_tmul]
    | add y z hy hz => simp [map_add, hy, hz]
  constructor
  intro x hx
  apply (Algebra.TensorProduct.basis R b).repr.injective
  ext i
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have hmem : (Algebra.TensorProduct.basis R b).repr x i ∈ (⊥ : Ideal R).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, key m i x]
    have hz : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k m) (AlgHom.id k B) x = 0 :=
      (h m hm).eq_zero _ (hx.map _)
    rw [hz]
    simp
  rwa [IsJacobsonRing.out inferInstance Ideal.isRadical_bot] at hmem

theorem isReduced_tensor_of_forall_finite {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (hB : ∀ (E : Type) [Field E] [Algebra k E] [FiniteDimensional k E], IsReduced (E ⊗[k] B))
    (A : Type) [CommRing A] [Algebra k A] [IsReduced A] : IsReduced (B ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro A₀ hfg
  have : Algebra.FiniteType k A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have : IsJacobsonRing A₀ := isJacobsonRing_of_finiteType (A := k)
  have : IsReduced A₀ := isReduced_of_injective A₀.val Subtype.val_injective
  have hA₀ : IsReduced (A₀ ⊗[k] B) := isReduced_tensor_of_forall_isMaximal fun m hm => by
    let := Ideal.Quotient.field m
    have := finite_of_finite_type_of_isJacobsonRing k (A₀ ⧸ m)
    exact hB (A₀ ⧸ m)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k B A₀).toAlgHom
    (Algebra.TensorProduct.comm k B A₀).injective

theorem isReduced_tensor_finite_finite {k : Type} [Field k] [CharZero k] (E E' : Type) [Field E]
    [Algebra k E] [Field E'] [Algebra k E'] [FiniteDimensional k E'] :
    IsReduced (E ⊗[k] E') := by
  have : Algebra.FormallyUnramified k E' := Algebra.FormallyUnramified.of_isSeparable k E'
  exact Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[k] E')

theorem proof : BaseChangeReduced.Statement := by
  intro k L A _ _ _ _ _ _ hA
  have step : ∀ (E' : Type) [Field E'] [Algebra k E'] [FiniteDimensional k E'] (A' : Type)
      [CommRing A'] [Algebra k A'] [IsReduced A'], IsReduced (E' ⊗[k] A') :=
    fun E' _ _ _ A' _ _ _ =>
      isReduced_tensor_of_forall_finite (B := E') (fun E _ _ _ => isReduced_tensor_finite_finite E E') A'
  exact isReduced_tensor_of_forall_finite (B := L) (fun E _ _ _ => step E L) A

end BaseChangeReduced

end SectionsLattice

end GroundTheory.Heights₂.Heights

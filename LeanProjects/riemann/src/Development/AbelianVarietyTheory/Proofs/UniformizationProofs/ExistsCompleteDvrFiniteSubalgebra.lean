import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPrecompleteOfLeOfPowLe

namespace GlobalTheory

namespace CompleteFiniteExtension

open IsLocalRing

theorem isPrecomplete_of_le_of_pow_le {A : Type*} [CommRing A] {I J : Ideal A} (hJ : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A := by
  first
  | (rename_i h_1 h_7; revert A h_1 I J hJ e he h_7; exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le)
  | exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | (apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le ..)

theorem isAdicComplete_of_finite_local (R S : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsAdicComplete (maximalIdeal S) S := by
  have := IsNoetherianRing.of_finite R S
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := R) S
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal S ^ e ≤ (maximalIdeal R).map (algebraMap R S) := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg (fun b hb => ?_) (IsNoetherian.noetherian _)
    obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := R) S b
      fun n hn => eq_maximalIdeal hn ▸ hb
    exact ⟨N, hN⟩
  have := isPrecomplete_of_le_of_pow_le
    (ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) S _ inferInstance) he
  exact ⟨⟩

end CompleteFiniteExtension

theorem exists_complete_dvr_finite_subalgebra :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] (F : Type) [Field F]
      [Algebra V F] [FaithfulSMul V F] [Algebra.IsAlgebraic V F] (s : Finset F),
      ∃ (W : Subalgebra V F) (_ : IsDiscreteValuationRing W),
        IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
        IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧
        Module.Finite V W ∧ Module.Free V W ∧ IsLocalHom (algebraMap V W) ∧
        (∀ x ∈ s, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) ∧
        ∀ x ∈ s, IsIntegral V x → x ∈ W := by
  intro V _ _ _ _ _ F _ _ _ _ s
  let K := FractionRing V
  let _ : Algebra K F := FractionRing.liftAlgebra V F
  have : IsScalarTower V K F := FractionRing.isScalarTower_liftAlgebra V F
  have : Algebra.IsAlgebraic K F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mp inferInstance
  let L : IntermediateField K F := IntermediateField.adjoin K (s : Set F)
  have : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let f : L →ₐ[V] F := L.val.restrictScalars V
  have hf : Function.Injective f := Subtype.val_injective
  let W : Subalgebra V F := (integralClosure V L).map f
  let e : integralClosure V L ≃ₐ[V] W := Subalgebra.equivMapOfInjective _ f hf
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  have hB : Module.Finite V (integralClosure V L) := IsIntegralClosure.finite V K L _
  have hBd : IsDiscreteValuationRing (integralClosure V L) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L
  have hfin : Module.Finite V W := Module.Finite.equiv e.toLinearEquiv
  have hd : IsDiscreteValuationRing W :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hmem : ∀ x ∈ L, IsIntegral V x → x ∈ W := fun x hx hi =>
    ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩
  have hsL : ∀ x ∈ s, x ∈ L := fun x hx => IntermediateField.subset_adjoin K _ hx
  refine ⟨W, hd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W,
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra W, hfin, inferInstance, inferInstance,
    fun x hx => ?_, fun x hx => hmem x (hsL x hx)⟩
  obtain ⟨y, hy, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := V) x).exists_integral_multiple
  refine ⟨y • x, hmem _ ?_ h, algebraMap V F y, W.algebraMap_mem y,
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective V F)).2 hy, ?_⟩
  · rw [← algebraMap_smul K y x]
    exact L.smul_mem (hsL x hx)
  · rw [Algebra.smul_def, mul_comm]

end GlobalTheory

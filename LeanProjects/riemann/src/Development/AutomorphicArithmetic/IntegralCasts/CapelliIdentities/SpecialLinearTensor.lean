import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpecialLinearMap

noncomputable def UpperTheory.Reformulated.B.SpecialLinearTensor.sl :
    {I : Type} →
      [Fintype I] →
        [dI : DecidableEq I] →
          {W : I → Type} →
            [inst : (i : I) → AddCommGroup (W i)] →
              [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
                (v : I) → ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] W v :=
    fun {I : Type} [Fintype I] [DecidableEq I] {W : I → Type} [(i : I) → AddCommGroup (W i)]
        [(i : I) → _root_.Module ℂ (W i)] (v : I) (f : (i : I) → Module.Dual ℂ (W i)) ↦
      (PiTensorProduct.lift : MultilinearMap ℂ W (W v) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] W v)
        (UpperTheory.Reformulated.B.SpecialLinearMap.slM v f)

theorem UpperTheory.Reformulated.B.SpecialLinearTensor.sl_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (v : I) (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.SpecialLinearTensor.sl v f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → W v)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        (∏ i ∈ Finset.univ.erase v, (f i : W i → ℂ) (m i)) • m v := by
  intro I _ _ W _ _ v f m
  exact PiTensorProduct.lift.tprod (φ := UpperTheory.Reformulated.B.SpecialLinearMap.slM v f) m

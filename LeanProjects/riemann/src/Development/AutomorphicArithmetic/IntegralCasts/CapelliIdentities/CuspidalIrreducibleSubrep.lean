import Mathlib

noncomputable def UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev :
    {I : Type} →
      [Fintype I] →
        {W : I → Type} →
          [inst : (i : I) → AddCommGroup (W i)] →
            [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
              ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ :=
    fun {I : Type} [Fintype I] {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
        (f : (i : I) → Module.Dual ℂ (W i)) ↦
      (PiTensorProduct.lift : MultilinearMap ℂ W ℂ → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] ℂ)
        ((MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap f)

theorem UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → ℂ)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        ∏ i : I, (f i : W i → ℂ) (m i) := by
  intro I _ _ W _ _ f m
  simp [UpperTheory.Reformulated.B.CuspidalIrreducibleSubrep.ev]

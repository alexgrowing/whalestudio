import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk34.MM :
    Nat → Nat → Type :=
    fun (P Q : Nat) ↦ Matrix (Sum (Fin P) (Fin Q)) (Sum (Fin P) (Fin Q)) Complex

theorem UpperTheory.Reformulated.B.Qk34.norm_le_sum :
    ∀ (P Q : Nat) (X : UpperTheory.Reformulated.B.Qk34.MM P Q),
      @LE.le Real Real.instLE
        (@Norm.norm (UpperTheory.Reformulated.B.Qk34.MM P Q)
          (@NormedRing.toNorm (UpperTheory.Reformulated.B.Qk34.MM P Q)
            (@Matrix.linftyOpNormedRing (Sum (Fin P) (Fin Q)) Complex
              (@instFintypeSum (Fin P) (Fin Q) (Fin.fintype P) (Fin.fintype Q))
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              fun (a b : Sum (Fin P) (Fin Q)) ↦
              @instDecidableEqSum (Fin P) (Fin Q) (instDecidableEqFin P) (instDecidableEqFin Q) a b))
          X)
        (∑ i : Sum (Fin P) (Fin Q), ∑ j : Sum (Fin P) (Fin Q), @Norm.norm Complex Complex.instNorm (X i j)) := by
  intro P Q X
  have h := Matrix.linfty_opNorm_def (A := X)
  refine le_trans (le_of_eq h) ?_
  have key : ((Finset.univ : Finset (Sum (Fin P) (Fin Q))).sup
      fun i => ∑ j : Sum (Fin P) (Fin Q), ‖X i j‖₊)
      ≤ ∑ i : Sum (Fin P) (Fin Q), ∑ j : Sum (Fin P) (Fin Q), ‖X i j‖₊ :=
    Finset.sup_le fun i hi =>
      Finset.single_le_sum (f := fun i => ∑ j : Sum (Fin P) (Fin Q), ‖X i j‖₊)
        (fun _ _ => by positivity) hi
  have key' := NNReal.coe_le_coe.mpr key
  simpa only [NNReal.coe_sum, coe_nnnorm] using key'

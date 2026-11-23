import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.GLFin

noncomputable section

namespace GlobalTheory.GLFin

theorem expGL_image_ball_mem_nhds : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ ε : ℝ, 0 < ε →
    (fun X : Lie E a => GlobalTheory.ExpDeriv.expGL X 1) '' {X | ‖X‖ < ε} ∈ nhds (1 : GL (Fin a) (Cinf E)) := by
  intro E _ _ _ a ε hε
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hd : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin a) (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] _)) 0 :=
    hasStrictFDerivAt_exp_zero
  have hmap0 := hd.map_nhds_eq_of_equiv
  rw [NormedSpace.exp_zero] at hmap0
  have hmap : Filter.map (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _) (nhds 0) =
      nhds (1 : Matrix (Fin a) (Fin a) (Cinf E)) := hmap0
  have hopen : IsOpen {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} :=
    isOpen_lt (continuous_norm.comp (continuous_id : Continuous fun X : Lie E a => X)) continuous_const
  have hball : {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} ∈
      nhds (0 : Matrix (Fin a) (Fin a) (Cinf E)) := hopen.mem_nhds (by simpa using hε)
  have himg : (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _) ''
      {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} ∈
      nhds (1 : Matrix (Fin a) (Fin a) (Cinf E)) := hmap ▸ Filter.image_mem_map hball
  have hpre := Units.continuous_val.continuousAt.preimage_mem_nhds (x := (1 : GL (Fin a) (Cinf E))) himg
  refine Filter.mem_of_superset hpre ?_
  rintro u ⟨X, hX, hXu⟩
  refine ⟨Matrix.of.symm X, hX, Units.ext ?_⟩
  rw [GlobalTheory.ExpDeriv.expGL_val, one_smul]
  exact hXu

end GlobalTheory.GLFin

end

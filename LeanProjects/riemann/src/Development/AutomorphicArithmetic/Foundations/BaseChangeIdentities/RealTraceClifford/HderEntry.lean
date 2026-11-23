import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

private theorem hder_entry {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j) ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  have hL := ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap).hasFDerivAt (x := NormedSpace.exp (t • X))
  exact hL.comp_hasDerivAt t h

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem UpperTheory.RealTr.basic :
    ∀ n : ℕ, IsOpen (GLs n) ∧ (∀ g : Mat n, g ∈ GLs n ↔ IsUnit g) ∧ (∀ X : Mat n, NormedSpace.exp X ∈ GLs n) ∧
      (∀ (X g : Mat n) (t : ℝ), HasDerivAt (fun s : ℝ => g * NormedSpace.exp (s • X)) (g * NormedSpace.exp (t • X) * X) t) ∧
      ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U)),
        (∀ g : G n, piM π g.val = π g) ∧ (∀ g ∈ GLs n, ∀ h ∈ GLs n, piM π (g * h) = piM π g * piM π h) ∧ piM π 1 = 1 ∧
        (∀ k : UK n, piM π k.1 = π (uG k)) ∧ ∀ v v' : U, (∀ w, coef π w v 1 = coef π w v' 1) → v = v' := by
  intro n
  have hmem : ∀ g : Mat n, g ∈ GLs n ↔ IsUnit g := by
    intro g
    simp only [GLs, Set.mem_setOf_eq]
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hval : ∀ {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U)) (g : G n),
      piM π g.val = π g := by
    intro U _ _ π g
    simp only [piM, dif_pos g.isUnit]
    congr 1
    exact Units.ext rfl
  refine ⟨?_, hmem, ?_, ?_, ?_⟩
  · exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  · intro X
    exact (hmem _).2 (Matrix.isUnit_exp X)
  · intro X g t
    refine (hasDerivAt_pi (φ := fun s : ℝ => (g * NormedSpace.exp (s • X) : Mat n))).2 fun i => ?_
    refine (hasDerivAt_pi (φ := fun s : ℝ => (g * NormedSpace.exp (s • X) : Mat n) i)).2 fun j => ?_
    have hs : HasDerivAt (fun s : ℝ => ∑ k, g i k * (NormedSpace.exp (s • X) : Mat n) k j)
        (∑ k, g i k * ((NormedSpace.exp (t • X) * X : Mat n) k j)) t :=
      HasDerivAt.fun_sum (fun k _ => (hder_entry X t k j).const_mul (g i k))
    have e1 : (fun s : ℝ => (g * NormedSpace.exp (s • X) : Mat n) i j) =
        fun s : ℝ => ∑ k, g i k * (NormedSpace.exp (s • X) : Mat n) k j := by
      funext s
      rfl
    have e2 : (g * NormedSpace.exp (t • X) * X : Mat n) i j =
        ∑ k, g i k * ((NormedSpace.exp (t • X) * X : Mat n) k j) := by
      rw [Matrix.mul_assoc]
      rfl
    show HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X) : Mat n) i j)
      ((g * NormedSpace.exp (t • X) * X : Mat n) i j) t
    rw [e1, e2]
    exact hs
  · intro U _ _ π
    have hone : piM π 1 = 1 := by
      have := hval π 1
      simpa using this
    refine ⟨hval π, ?_, hone, ?_, ?_⟩
    · intro g hg h hh
      have ug := (hmem g).1 hg
      have uh := (hmem h).1 hh
      have := hval π (ug.unit * uh.unit)
      simp only [Units.val_mul, IsUnit.unit_spec, map_mul] at this
      rw [this, ← hval π ug.unit, ← hval π uh.unit]
      simp
    · intro k
      exact hval π (uG k)
    · intro v v' h
      apply ext_inner_left ℂ
      intro w
      have := h w
      simpa [coef, hone] using this

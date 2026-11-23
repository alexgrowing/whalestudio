import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem cast_ne_nat {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

private theorem std_eq (r s : ℕ) : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv :=
  Equiv.ext fun _ => rfl

open UpperTheory.V.Af.Fin in
private theorem lev_left {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, 1) = emb (e1 r s) x := by
  refine Units.ext ?_
  rw [GlobalTheory.SmGL.val_emb₂, coe_emb, std_eq]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have := matrixExtendByZero_apply (e1 r s) (x.val - 1) i j
    simp only [orderedCechToCatCochainsOne_apply_valueAtSubset] at this
    simp [this, Matrix.one_apply]
  · rw [Matrix.add_apply, matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cast_ne_nat k j).symm]
    simp [Matrix.one_apply, cast_ne_nat]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cast_ne_nat k i).symm]
    simp [Matrix.one_apply, (cast_ne_nat _ _).symm]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cast_ne_nat k i).symm]
    simp [Matrix.one_apply]

open UpperTheory.V.Af.Fin in
private theorem lev_right {R : Type} [CommRing R] {r s : ℕ} (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (1, y) = emb (e2 r s) y := by
  refine Units.ext ?_
  rw [GlobalTheory.SmGL.val_emb₂, coe_emb, std_eq]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => cast_ne_nat i k]
    simp [Matrix.one_apply]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => cast_ne_nat i k]
    simp [Matrix.one_apply, cast_ne_nat]
  · rw [Matrix.add_apply, matrixExtendByZero_apply_of_outside_col _ _ _ fun k => cast_ne_nat j k]
    simp [Matrix.one_apply, (cast_ne_nat _ _).symm]
  · have := matrixExtendByZero_apply (e2 r s) (y.val - 1) i j
    simp only [alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
    simp [this, Matrix.one_apply]

private theorem lev_eq_blk {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, y) = blk x y := by
  rw [blk, ← lev_left, ← lev_right, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem UpperTheory.V.Cj.S.capBlock :
    UpperTheory.V.Cj.S.CapBlock := by
  intro E _ _ _ r s ψ hψ t u x y
  have h := GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi E r s t u ψ (fun X g => by
    have e : unip X = unipGL (fun p : UPos (r + s) r => X ⟨p.1, p.2.1, p.2.2⟩) := Units.ext rfl
    rw [e]
    exact hψ _ g) (x, y)
  rw [lev_eq_blk] at h
  exact h

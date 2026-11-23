import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinfStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrobIntegralCoeff

section Generic

variable {R O : Type} [CommRing R] [CommRing O] [Algebra R O] {I : Type} [Fintype I] [DecidableEq I]
  (b : Module.Basis I R O)

def regRep (W : Type) [CommRing W] [Algebra R W] : O ⊗[R] W →ₐ[R] Matrix I I W :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId R W)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom R W (Matrix I I W))
    (fun _ w => (Algebra.commutes w _).symm)

variable {W W' : Type} [CommRing W] [Algebra R W] [CommRing W'] [Algebra R W']

theorem regRep_tmul (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = Algebra.leftMulMatrix b o i j • w := by
  erw [Algebra.TensorProduct.lift_tmul]
  simp [Algebra.smul_def, Matrix.algebraMap_eq_diagonal, Matrix.mul_diagonal, mul_comm]

theorem regRep_map (f : W →ₐ[R] W') (z : O ⊗[R] W) (i j : I) :
    regRep b W' (Algebra.TensorProduct.map (AlgHom.id O O) f z) i j = f (regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, regRep_tmul, regRep_tmul, map_smul]
  | add x y hx hy => simp [map_add, Matrix.add_apply, hx, hy]

private theorem regRep_tmul' (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = b.repr (o * b j) i • w := by
  rw [regRep_tmul, Algebra.leftMulMatrix_eq_repr_mul]

theorem eq_sum_regRep (z : O ⊗[R] W) :
    z = ∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp_rw [regRep_tmul', ← TensorProduct.smul_tmul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, ← TensorProduct.sum_tmul, b.sum_repr, TensorProduct.smul_tmul',
      ← TensorProduct.sum_tmul]
    congr 1
    simp_rw [← mul_smul_comm, ← Finset.mul_sum, b.sum_repr, mul_one]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp [map_add, Matrix.add_apply, TensorProduct.tmul_add, smul_add, Finset.sum_add_distrib]

theorem mem_range_of_regRep (f : W →ₐ[R] W') (z : O ⊗[R] W')
    (h : ∀ i j, regRep b W' z i j ∈ Set.range f) :
    z ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  choose g hg using h
  refine ⟨∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] g i j), ?_⟩
  conv_rhs => rw [eq_sum_regRep b z]
  simp_rw [TensorProduct.smul_tmul', map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hg]

def blow {p q : Type} (Z : Matrix p q (O ⊗[R] W)) : Matrix (p × I) (q × I) W :=
  Matrix.of fun x y => regRep b W (Z x.1 y.1) x.2 y.2

theorem blow_map {p q : Type} (f : W →ₐ[R] W') (Z : Matrix p q (O ⊗[R] W)) :
    blow b (Z.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) = (blow b Z).map f := by
  ext x y
  simp [blow, regRep_map]

theorem blow_add {p q : Type} (Z Z' : Matrix p q (O ⊗[R] W)) :
    blow b (Z + Z') = blow b Z + blow b Z' := by
  ext x y
  simp [blow, map_add]

theorem blow_mul {p q r : Type} [Fintype q] (Z : Matrix p q (O ⊗[R] W))
    (Z' : Matrix q r (O ⊗[R] W)) : blow b (Z * Z') = blow b Z * blow b Z' := by
  ext x y
  simp [blow, Matrix.mul_apply, map_sum, Matrix.sum_apply, Fintype.sum_prod_type]

omit b [Fintype I] [DecidableEq I] in

theorem integrality_baseChange [Module.Free R O] [Module.Finite R O] (f : W →ₐ[R] W')
    (φ : W' →ₐ[R] W')
    (H : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q W') (S : Matrix p p W)
      (S' : Matrix q q W) (Y : Matrix p q W),
      Z.map φ = S.map f * Z * S'.map f + Y.map f → ∀ a b, Z a b ∈ Set.range f)
    (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (O ⊗[R] W')) (S : Matrix p p (O ⊗[R] W))
    (S' : Matrix q q (O ⊗[R] W)) (Y : Matrix p q (O ⊗[R] W))
    (h : Z.map (Algebra.TensorProduct.map (AlgHom.id O O) φ) =
      S.map (Algebra.TensorProduct.map (AlgHom.id O O) f) * Z *
        S'.map (Algebra.TensorProduct.map (AlgHom.id O O) f) +
      Y.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) (x : p) (y : q) :
    Z x y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R (O ⊗[R] W')
    exact ⟨0, Subsingleton.elim _ _⟩
  classical
  let c := Module.Free.chooseBasis R O
  have key := congrArg (blow c) h
  rw [blow_map, blow_add, blow_mul, blow_mul, blow_map, blow_map, blow_map] at key
  apply mem_range_of_regRep c f (Z x y)
  intro i j
  exact H _ _ (blow c Z) (blow c S) (blow c S') (blow c Y) key (x, i) (y, j)

private theorem module_free_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Free ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  have : Module.IsTorsionFree ℤ_[l] K := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  exact IsIntegralClosure.module_free ℤ_[l] ℚ_[l] K _

private theorem module_finite_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Finite ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] K _

end Generic

theorem frobenius_integrality_coeff : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (RW LL)) (S : Matrix p p (RA LL)) (S' : Matrix q q (RA LL)) (Y : Matrix p q (RA LL)), Z.map (φRW LL) = S.map (inclR LL) * Z * S'.map (inclR LL) + Y.map (inclR LL) → ∀ a b, Z a b ∈ Set.range (inclR LL) := by
  intro l _ LL p q _ _ Z S S' Y h a b
  unfold RW RA inclR φRW at *
  have := module_free_zpadic_OL l LL
  have := module_finite_zpadic_OL l LL
  exact integrality_baseChange (R := ℤ_[l]) (O := OL LL) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => GlobalTheory.T.frobeniusIntegrality_wittTilt_ainf l p q Z S S' Y h) p q Z S S' Y h a b

end GlobalTheory.FrobIntegralCoeff

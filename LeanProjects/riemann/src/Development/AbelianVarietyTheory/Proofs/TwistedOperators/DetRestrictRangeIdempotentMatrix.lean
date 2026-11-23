import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS

noncomputable section

open Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.RegSS.IdemDet

theorem exists_factor {F m : Type} [Field F] [Fintype m] [DecidableEq m] (p : Matrix m m F)
    (h0 : p ≠ 0) (hp : p * p = p) :
    ∃ (d : ℕ) (A : Matrix m (Fin d) F) (B : Matrix (Fin d) m F), 0 < d ∧ A * B = p ∧ B * A = 1 := by
  let f := Matrix.toLin' p
  let c := Module.finBasis F (LinearMap.range f)
  let e := Pi.basisFun F m
  have hAB : LinearMap.toMatrix c e (LinearMap.range f).subtype *
      LinearMap.toMatrix e c f.rangeRestrict = p := by
    rw [← LinearMap.toMatrix_comp, show (LinearMap.range f).subtype ∘ₗ f.rangeRestrict = f from rfl]
    simp [e, f]
  refine ⟨_, _, _, ?_, hAB, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => h0 ?_
    haveI : IsEmpty (Fin (Module.finrank F (LinearMap.range f))) := by rw [h]; infer_instance
    rw [← hAB]; ext i j; simp [Matrix.mul_apply]
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id c]
    congr 1
    ext ⟨_, v, rfl⟩ : 2
    simp [f, hp]

theorem det_smul_idem {R m : Type} [CommRing R] [Fintype m] [DecidableEq m] {d : ℕ}
    (A : Matrix m (Fin d) R) (B : Matrix (Fin d) m R) (h : B * A = 1) (t : R) :
    (t • (A * B) + 1 - A * B).det = t ^ d := by
  have e : t • (A * B) + 1 - A * B = 1 + ((t - 1) • A) * B := by
    rw [Matrix.smul_mul, sub_smul, one_smul]; abel
  rw [e, Matrix.det_one_add_mul_comm, Matrix.mul_smul, h, sub_smul, one_smul, add_sub_cancel]
  simp

section Rep

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

def regRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    E ⊗[F] R →ₐ[F] Matrix ι ι R :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId F R)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom F R (Matrix ι ι R))
    (fun _ a => (Algebra.commutes a _).symm)

theorem regRep_tmul (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] (x : E) (t : R) :
    regRep b R (x ⊗ₜ t) = t • (Algebra.leftMulMatrix b x).map (algebraMap F R) := by
  refine (Algebra.TensorProduct.lift_tmul _ _ _ x t).trans ?_
  rw [IsScalarTower.toAlgHom_apply, ← Algebra.commutes, ← Algebra.smul_def]
  rfl

theorem continuous_regRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] :
    @Continuous _ _ (Formalism.BasicNotions.tensTopL (F := F) (E := E) R) _ (regRep b R) := by
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  letI := moduleTopology R (E ⊗[F] R)
  haveI : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := R) (regRep b R).toRingHom ?_
  have : ⇑((regRep b R).toRingHom.comp (algebraMap R (E ⊗[F] R))) =
      fun t : R => t • (Algebra.leftMulMatrix b 1).map (algebraMap F R) :=
    funext fun t => regRep_tmul b R 1 t
  rw [this]
  fun_prop

variable {n : Type} [Fintype n] [DecidableEq n]

def blockRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    Matrix n n (E ⊗[F] R) →+* Matrix (n × ι) (n × ι) R :=
  (Matrix.compRingEquiv n ι R).toRingHom.comp (regRep b R).toRingHom.mapMatrix

def blockRat (b : Module.Basis ι F E) : Matrix n n E →+* Matrix (n × ι) (n × ι) F :=
  (Matrix.compRingEquiv n ι F).toRingHom.comp (Algebra.leftMulMatrix b).toRingHom.mapMatrix

theorem blockRep_apply (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (g : Matrix n n (E ⊗[F] R)) (i j : n × ι) :
    blockRep b R g i j = regRep b R (g i.1 j.1) i.2 j.2 := rfl

theorem blockRat_apply (b : Module.Basis ι F E) (g : Matrix n n E) (i j : n × ι) :
    blockRat b g i j = Algebra.leftMulMatrix b (g i.1 j.1) i.2 j.2 := rfl

theorem blockRat_injective (b : Module.Basis ι F E) :
    Function.Injective (blockRat (n := n) b) := by
  intro g h e
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext k l
  exact congrFun (congrFun e (i, k)) (j, l)

theorem blockRep_map (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (g : Matrix n n E) :
    blockRep b R (g.map (inclE (F := F) R)) = (blockRat b g).map (algebraMap F R) := by
  ext i j
  rw [blockRep_apply, Matrix.map_apply, Matrix.map_apply, blockRat_apply]
  change regRep b R (g i.1 j.1 ⊗ₜ 1) _ _ = _
  rw [regRep_tmul, one_smul, Matrix.map_apply]

theorem blockRep_smul (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (t : R) (g : Matrix n n (E ⊗[F] R)) :
    blockRep b R (((1 : E) ⊗ₜ[F] t) • g) = t • blockRep b R g := by
  ext i j
  rw [blockRep_apply, Matrix.smul_apply, Matrix.smul_apply, blockRep_apply, smul_eq_mul, map_mul,
    regRep_tmul, map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_apply]

end Rep

end GlobalTheory.RegSS.IdemDet

namespace GlobalTheory.RegSS

open IdemDet

theorem idempotentDet : IdempotentDet := by
  intro F E _ _ _ _ n _ _ ε h0 hε R _ _ _ _
  letI : TopologicalSpace (E ⊗[F] R) := Formalism.BasicNotions.tensTopL (F := F) (E := E) R
  let b := Module.finBasis F E
  have hq : blockRat b ε * blockRat b ε = blockRat b ε := by rw [← map_mul, hε]
  obtain ⟨d, A, B, hd, hAB, hBA⟩ := exists_factor (blockRat b ε)
    (fun h => h0 (blockRat_injective b (by rw [h, map_zero]))) hq
  set p := blockRep b R (ε.map (inclE (F := F) R)) with hp
  have hpq : p = (blockRat b ε).map (algebraMap F R) := blockRep_map b R ε
  have hpp : p * p = p := by rw [hpq, ← Matrix.map_mul, hq]
  refine ⟨d, fun g => (blockRep b R g * p + 1 - p).det, hd, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (blockRep (n := n) b R) := by
      refine continuous_matrix fun i j => ?_
      exact ((continuous_regRep b R).comp (continuous_id.matrix_elem i.1 j.1)).matrix_elem i.2 j.2
    exact (((hc.matrix_mul continuous_const).add continuous_const).sub continuous_const).matrix_det
  · simp
  · intro g h hh
    have hc : blockRep b R h * p = p * blockRep b R h := by
      rw [hp, ← map_mul, ← map_mul, hh]
    have h1 : p * (blockRep b R h * p) = blockRep b R h * p := by
      rw [← mul_assoc, ← hc, mul_assoc, hpp]
    simp only
    rw [← Matrix.det_mul, map_mul]
    congr 1
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc, h1, hpp, mul_one, one_mul]
    abel
  · intro g
    refine ⟨(blockRat b g * blockRat b ε + 1 - blockRat b ε).det, ?_⟩
    simp only
    rw [RingHom.map_det, map_sub, map_add, map_mul, map_one, blockRep_map, hpq]
    rfl
  · intro g t hg
    have h1 : blockRep b R g * p = t • p := by
      rw [hp, ← map_mul, hg, blockRep_smul]
    simp only
    rw [h1, hpq, ← hAB, Matrix.map_mul]
    refine det_smul_idem _ _ ?_ t
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RegSS

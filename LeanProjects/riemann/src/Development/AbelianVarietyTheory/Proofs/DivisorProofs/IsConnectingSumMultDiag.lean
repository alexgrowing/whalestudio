import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycle

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
  [IsCocomm R A] [IsCocomm R B]

variable (R A) in

abbrev multDiag (i : ℕ) : A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lift (mulBy R A i : A →ₐ[R] A) (AlgHom.id R _) (fun _ _ ↦ Commute.all _ _)

variable (R A) in

abbrev valZero : A ⊗[R] A →ₐ[R] R :=
  Algebra.TensorProduct.lift (counitAlgHom R A) (counitAlgHom R A) (fun _ _ ↦ Commute.all _ _)

theorem map_multDiag (f : A →ₐc[R] B) (i : ℕ) (c : A ⊗[R] A) :
    f (multDiag R A i c) = multDiag R B i (pullbackTwo f c) := by
  induction c with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp [map_mulBy]

omit [IsCocomm R A] [IsCocomm R B] in

theorem valZero_pullTwo (f : A →ₐc[R] B) (c : A ⊗[R] A) :
    valZero R B (pullbackTwo f c) = valZero R A c := by
  induction c with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp

theorem counit_multDiag (i : ℕ) (c : A ⊗[R] A) :
    counit (R := R) (multDiag R A i c) = valZero R A c := by
  induction c with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp

theorem pullTwo_mulBy_eq (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) (k : ℕ) :
    pullbackTwo (mulBy R A k) c = algebraMap R _ (valZero R A c) + k • c +
      cobOne R A (∑ i ∈ Finset.range k, multDiag R A i c) := by
  induction k with
  | zero =>
    have h0 : ∀ a : A, mulBy R A 0 a = algebraMap R A (counit a) := fun _ => rfl
    rw [Finset.sum_range_zero, map_zero, zero_smul, add_zero, add_zero]
    generalize c = t
    induction t with
    | zero => simp
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul a b =>
      simp [h0, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
        smul_smul, mul_comm]
  | succ k ih =>
    have h := pullTwo_convMul (mulBy R A k) (BialgHom.id R A) c hc
    have e : (toConv (mulBy R A k) * toConv (BialgHom.id R A)).ofConv = mulBy R A (k + 1) := by
      rw [mulBy, mulBy, pow_succ]
    have e2 : ∀ t : A ⊗[R] A, LinearMap.mul' R A (TensorProduct.map (mulBy R A k : A →ₗ[R] A)
        (BialgHom.id R A : A →ₗ[R] A) t) = multDiag R A k t := fun t => by
      induction t with
      | zero => simp
      | add s t hs ht => simp only [map_add, hs, ht]
      | tmul a b => simp
    rw [e, e2, pullTwo_id, ih] at h
    rw [h, Finset.sum_range_succ, map_add, succ_nsmul]
    abel

end PDiv

namespace PDivGroup

open PDiv

theorem isConnecting_sum_multDiag (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hp : (p : R) = 0)
    (G : PDivGroup p R) (z : G.cocycles) :
    G.IsConnecting (Submodule.Quotient.mk z) (∑ i ∈ Finset.range p,
      Algebra.TensorProduct.lift (mulBy R (G.A 1) i : G.A 1 →ₐ[R] G.A 1) (AlgHom.id R _)
        (fun _ _ ↦ Commute.all _ _) (z.1 1)) := by
  let B : G.funs := ⟨fun n => ∑ i ∈ Finset.range p, multDiag R (G.A n) i (z.1 n), fun n => by
    simp only [map_sum, map_multDiag, (z.2 n).2]⟩
  let K : G.funs := ⟨fun n => algebraMap R _ (valZero R _ (z.1 n)), fun n => by
    dsimp only
    rw [AlgHomClass.commutes, ← (z.2 n).2, valZero_pullTwo]⟩
  have hK : funsMap ((p : ℤ_[p]) • 𝟙 G) K = K :=
    Subtype.ext (funext fun n => AlgHomClass.commutes (Hom.app _ n) _)
  refine ⟨z + G.cob K, B, (Submodule.Quotient.eq _).2 ⟨K, by simp⟩, ?_, ?_, rfl⟩
  · rw [map_add, cocyclesMap_cob, hK]
    refine Subtype.ext (funext fun n => ?_)
    change cobOne R _ (B.1 n) = pullbackTwo (((p : ℤ_[p]) • 𝟙 G : G ⟶ G).app n) (z.1 n) +
      cobOne R _ (algebraMap R _ (valZero R _ (z.1 n)))
    rw [natCast_smul_id_app, pullTwo_mulBy_eq _ (z.2 n).1, ← Nat.cast_smul_eq_nsmul R, hp,
      zero_smul, add_zero, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      map_smul, cobOne_apply 1, comul_one, Algebra.TensorProduct.one_def, sub_self, zero_sub,
      smul_neg]
    abel
  · simp only [map_sum, counit_multDiag, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hp,
      zero_mul]

end PDivGroup

end GlobalTheory

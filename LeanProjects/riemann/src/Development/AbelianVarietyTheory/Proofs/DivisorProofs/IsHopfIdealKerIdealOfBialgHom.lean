import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal_of_bialgHom (k A B : Type) [CommRing k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] (f : B →ₐc[k] A) : (kerIdeal f).IsHopfIdeal k where
  counit_eq_zero x hx :=
    (kerIdeal_le_ker_iff f (counitAlgHom k A)).2 (fun c => by simp) hx
  map_mkQ_comul_eq_zero x hx := by
    have h0 := (kerIdeal_le_ker_iff f (Ideal.Quotient.mkₐ k (kerIdeal f))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    have h : kerIdeal f ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f))).comp (comulAlgHom k A)) := by
      refine (kerIdeal_le_ker_iff f _).2 fun c => ?_
      have key : ∀ t : B ⊗[k] B, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f)) (pullbackTwo f t) =
          algebraMap k _ (counit (R := k)
            (TensorProduct.lid k B (LinearMap.rTensor B (counit (R := k) (A := B)) t))) := by
        intro t
        induction t with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
          rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
            TensorProduct.lid_tmul, map_smul]
          erw [h0, h0]
          simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
            smul_smul, mul_comm]
      rw [AlgHom.comp_apply, comulAlgHom_apply, ← pullTwo_comul, key, rTensor_counit_comul,
        TensorProduct.lid_tmul, one_smul]
    exact h hx
  antipode_mem x hx := by
    have h : kerIdeal f ≤ (kerIdeal f).comap (HopfAlgebra.antipodeAlgHom k A) := by
      refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      have ha' : counit (R := k) a = 0 := ha
      change HopfAlgebra.antipode k (f a) ∈ kerIdeal f
      rw [← bialgHom_map_antipode]
      exact Ideal.mem_map_of_mem (f : B →ₐ[k] A) (by simp [RingHom.mem_ker, ha'])
    exact h hx

end GlobalTheory.PDiv

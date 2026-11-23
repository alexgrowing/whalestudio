import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfHeightOnePrimitiveEqZeroOfZeroDifferentialStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerPrim

theorem mem_frobKerIdeal_of_cobOne (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H] (b : H)
    (_hb : counit (R := K) b = 0) (hd : dUnit K b = 0)
    (hc : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
      (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0) :
    b ∈ frobKerIdeal p K H := by
  haveI := FrobKerOrder.isHopfIdeal p K H
  set J := frobKerIdeal p K H with hJ
  let π : H →ₐc[K] H ⧸ J := Bialgebra.Quotient.mkBialgHom J
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsCocomm K (H ⧸ J) := by
    constructor
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπ y
    have h1 := pullTwo_comul π x
    simp only [LinearMap.comp_apply]
    rw [← h1]
    simp only [pullbackTwo]
    have h2 := TensorProduct.map_comm (π : H →ₗ[K] H ⧸ J) (π : H →ₗ[K] H ⧸ J) (comul x)
    rw [comm_comul] at h2
    exact h2.symm
  have hpow : ∀ a ∈ augIdeal K (H ⧸ J), a ^ p = 0 := by
    intro a ha
    obtain ⟨x, rfl⟩ := hπ a
    have hx : x ∈ augIdeal K H := ha
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have hc' : cobOne K (H ⧸ J) (π b) = 0 := by
    rw [← pullTwo_cobOne]
    exact hc
  have hd' : dUnit K (π b) = 0 := by
    rw [← cotMap_d, hd, map_zero]
  have h0 := GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential p K (H ⧸ J) hpow (π b) hc' hd'
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

end GlobalTheory.PDiv.FrobKerPrim

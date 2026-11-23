import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom

set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_hopf_quotient_torsionIdeal :
    ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
      ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
        Function.Surjective π ∧ RingHom.ker π = torsionIdeal O B n := by
  intro O _ B _ _ _ n
  haveI : (torsionIdeal O B n).IsHopfIdeal O :=
    isHopfIdeal_kerIdeal_of_bialgHom O B B (mulBy O B n)
  let π : B →ₐc[O] B ⧸ torsionIdeal O B n := Bialgebra.Quotient.mkBialgHom _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have cocomm : IsCocomm O (B ⧸ torsionIdeal O B n) :=
    { comm_comp_comul := LinearMap.ext fun b => by
        obtain ⟨a, rfl⟩ := hπ b
        have h : ∀ t : B ⊗[O] B,
            TensorProduct.comm O (B ⧸ torsionIdeal O B n) (B ⧸ torsionIdeal O B n) (TensorProduct.map (π : B →ₗ[O] B ⧸ torsionIdeal O B n) (π : B →ₗ[O] B ⧸ torsionIdeal O B n) t) =
            TensorProduct.map (π : B →ₗ[O] B ⧸ torsionIdeal O B n) (π : B →ₗ[O] B ⧸ torsionIdeal O B n) (TensorProduct.comm O B B t) := by
          intro t
          induction t with
          | zero => simp
          | add x y hx hy => simp only [map_add, hx, hy]
          | tmul x y => simp
        change TensorProduct.comm O (B ⧸ torsionIdeal O B n) (B ⧸ torsionIdeal O B n) (comul (π a)) = comul (π a)
        rw [← CoalgHomClass.map_comp_comul_apply π a, h, comm_comul] }
  exact ⟨B ⧸ torsionIdeal O B n, inferInstance, inferInstance,
    cocomm, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem⟩

end GlobalTheory.PDiv

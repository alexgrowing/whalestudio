import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFrobeniusPullbackCotangentModVersc
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

noncomputable section

namespace GlobalTheory.HopfQuot

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A] [IsCocomm k A]
  [Module.Finite k A] {C : Type} [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
  (π : A →ₐc[k] C)

instance isHopfIdeal_dual : (kerIdeal (CartierDual.map π)).IsHopfIdeal k := isHopfIdeal_kerIdeal _

abbrev proj : CartierDual k A →ₐc[k] CartierDual k A ⧸ kerIdeal (CartierDual.map π) :=
  Bialgebra.Quotient.mkBialgHom _

instance isCocomm_quot : IsCocomm k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) :=
  isCocomm_of_surjective (proj π) Ideal.Quotient.mk_surjective

def quotMap : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) →ₐc[k] A :=
  ((CartierDual.bidual k A).symm : _ →ₐc[k] A).comp (CartierDual.map (proj π))

theorem apply_quotMap (y : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)))
    (φ : CartierDual k A) : φ (quotMap π y) = y (proj π φ) := by
  simp [quotMap]

theorem proj_map (ψ : CartierDual k C) :
    proj π (CartierDual.map π ψ) = algebraMap k _ (counit (R := k) ψ) := by
  have hmem : CartierDual.map π ψ - algebraMap k _ (counit (R := k) ψ) ∈
      kerIdeal (CartierDual.map π) := by
    have h : CartierDual.map π ψ - algebraMap k _ (counit (R := k) ψ) =
        CartierDual.map π (ψ - algebraMap k _ (counit (R := k) ψ)) := by
      rw [map_sub, AlgHomClass.commutes]
    rw [h]
    exact Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])
  rw [← sub_eq_zero, ← AlgHomClass.commutes (proj π), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hmem

theorem quotMap_trivial (y : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π))) :
    π (quotMap π y) = algebraMap k C (counit (R := k) y) := by
  refine CartierDual.eq_of_forall_apply (R := k) fun ψ => ?_
  have h1 : ψ (π (quotMap π y)) = (CartierDual.map π ψ) (quotMap π y) := rfl
  rw [h1, apply_quotMap, proj_map, CartierDual.counit_apply, CartierDual.counit_apply,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, map_smul]
  simp [mul_comm]

theorem mem_range_quotMap {a : A} (ha : ∀ x ∈ kerIdeal (CartierDual.map π), x a = 0) :
    a ∈ Set.range (quotMap π) := by
  have hann : (CartierDual.bidual k A a).ofConv ∈
      (LinearMap.ker (proj π : CartierDual k A →ₐ[k] CartierDual k A ⧸ kerIdeal (CartierDual.map π)).toLinearMap).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have hx' : x ∈ kerIdeal (CartierDual.map π) :=
      Ideal.Quotient.eq_zero_iff_mem.1 (LinearMap.mem_ker.1 hx)
    exact ha x hx'
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
  obtain ⟨y, hy⟩ := hann
  refine ⟨WithConv.toConv y, ?_⟩
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  rw [apply_quotMap]
  exact LinearMap.congr_fun hy φ

theorem mul_map_apply {D : Type} [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A)
    (hf : kerIdeal f ≤ RingHom.ker π) (d : D) (r : CartierDual k A) (ψ : CartierDual k C) :
    (r * CartierDual.map π ψ) (f d) = r (f d) * ψ 1 := by
  have hπf := (kerIdeal_le_ker_iff f (π : A →ₐ[k] C)).1 hf
  have key : ∀ t : D ⊗[k] D, CartierDual.pair k A A (r ⊗ₜ CartierDual.map π ψ)
      (TensorProduct.map (f : D →ₗ[k] A) (f : D →ₗ[k] A) t) =
      r (f (TensorProduct.rid k D (LinearMap.lTensor D (counit (R := k) (A := D)) t))) * ψ 1 := by
    intro t
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_mul]
    | tmul x y =>
      rw [TensorProduct.map_tmul, CartierDual.pair_tmul_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, CartierDual.map_apply]
      have h1 : π (f y) = algebraMap k C (counit (R := k) y) := hπf y
      erw [h1]
      rw [map_smul, map_smul, Algebra.algebraMap_eq_smul_one, map_smul]
      simp only [smul_eq_mul]
      have hfx : (f : D →ₗ[k] A) x = f x := rfl
      rw [hfx]
      ring
  rw [CartierDual.mul_apply]
  have hc : comul (R := k) (f d) = TensorProduct.map (f : D →ₗ[k] A) (f : D →ₗ[k] A) (comul d) :=
    (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) d).symm
  rw [hc, key, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

theorem ideal_apply_eq_zero {D : Type} [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A)
    (hf : kerIdeal f ≤ RingHom.ker π) (d : D) :
    ∀ x ∈ kerIdeal (CartierDual.map π), x (f d) = 0 := by
  intro x hx
  suffices h : ∀ r : CartierDual k A, (r * x) (f d) = 0 by simpa using h 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, rfl⟩ := hx
    intro r
    have hψ' : ψ 1 = 0 := hψ
    erw [mul_map_apply π f hf d r ψ]
    rw [hψ', mul_zero]
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; simp [mul_add, hx r, hy r]
  | smul s x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx (r * s)

theorem ideal_eq_of_le_of_finrank_eq {R : Type} [CommRing R] [Algebra k R] [Module.Finite k R]
    {I J : Ideal R} (hIJ : I ≤ J)
    (h : Module.finrank k (R ⧸ I) = Module.finrank k (R ⧸ J)) : I = J := by
  have h1 := Submodule.finrank_quotient_add_finrank (I.restrictScalars k)
  have h2 := Submodule.finrank_quotient_add_finrank (J.restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k I).finrank_eq] at h1
  rw [(Submodule.Quotient.restrictScalarsEquiv k J).finrank_eq] at h2
  have hle : I.restrictScalars k ≤ J.restrictScalars k := hIJ
  exact Submodule.restrictScalars_injective k R R
    (Submodule.eq_of_le_of_finrank_eq hle (by omega))

theorem finrank_cartierDual (M : Type) [AddCommGroup M] [Module k M] [FiniteDimensional k M] :
    Module.finrank k (CartierDual k M) = Module.finrank k M :=
  (CartierDual.toDual k M).finrank_eq.trans Subspace.dual_finrank_eq

theorem quotMap_injective : Function.Injective (quotMap π) := by
  intro x y hxy
  have h := congrArg (CartierDual.bidual k A) hxy
  simp only [quotMap, BialgHom.comp_apply] at h
  erw [BialgEquiv.apply_symm_apply, BialgEquiv.apply_symm_apply] at h
  exact CartierDual.map_injective_of_surjective (f := proj π) Ideal.Quotient.mk_surjective h

theorem exists_quotient : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A]
    [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (π : A →ₐc[k] C), Function.Surjective π → ∃ (B : Type) (_ : CommRing B)
    (_ : HopfAlgebra k B) (_ : IsCocomm k B) (_ : Module.Finite k B) (j : B →ₐc[k] A),
    Function.Injective j ∧ kerIdeal j = RingHom.ker π ∧ ∀ (D : Type) [CommRing D]
    [Bialgebra k D] (f : D →ₐc[k] A), kerIdeal f ≤ RingHom.ker π → ∀ d, f d ∈ Set.range j := by
  intro k _ A _ _ _ _ C _ _ _ _ π hπ
  have hinj := quotMap_injective π
  refine ⟨CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)), inferInstance,
    inferInstance, inferInstance, inferInstance, quotMap π, hinj, ?_, ?_⟩
  · have hle : kerIdeal (quotMap π) ≤ RingHom.ker π :=
      (kerIdeal_le_ker_iff _ (π : A →ₐ[k] C)).2 (quotMap_trivial π)
    refine ideal_eq_of_le_of_finrank_eq (k := k) hle ?_
    have hA := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k A _ (quotMap π)
    have hD := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k (CartierDual k A) (CartierDual k C) (CartierDual.map π)
    rw [LinearMap.finrank_range_of_inj (f := ((quotMap π : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) →ₐ[k] A)).toLinearMap)
      (by exact hinj),
      finrank_cartierDual] at hA
    rw [LinearMap.finrank_range_of_inj (f := ((CartierDual.map π : CartierDual k C →ₐ[k] CartierDual k A)).toLinearMap)
      (by exact CartierDual.map_injective_of_surjective hπ), finrank_cartierDual,
      finrank_cartierDual] at hD
    have hC : Module.finrank k (A ⧸ RingHom.ker π) = Module.finrank k C :=
      (Ideal.quotientKerAlgEquivOfSurjective (f := (π : A →ₐ[k] C)) hπ).toLinearEquiv.finrank_eq
    haveI : Nontrivial A := RingHom.domain_nontrivial (counitAlgHom k A : A →+* k)
    have hpos : 0 < Module.finrank k A := Module.finrank_pos
    rw [hC]
    have hQ : 0 < Module.finrank k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)))
        with h0 | h0
      · rw [h0, mul_zero] at hD; omega
      · exact h0
    exact Nat.eq_of_mul_eq_mul_left hQ (by rw [← hA, hD, mul_comm])
  · intro D _ _ f hf d
    exact mem_range_quotMap π (ideal_apply_eq_zero π f hf d)

end GlobalTheory.HopfQuot

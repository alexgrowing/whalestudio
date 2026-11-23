import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv.FrobKerInter

theorem isHopfIdeal_sup {k A : Type} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (I J : Ideal A) [I.IsHopfIdeal k] [J.IsHopfIdeal k] : (I ⊔ J).IsHopfIdeal k where
  counit_eq_zero x hx := by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 := Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) hy
    have h2 := Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars k) hz
    rw [map_add, h1, h2, add_zero]
  map_mkQ_comul_eq_zero x hx := by
    set K := (I ⊔ J).restrictScalars k
    have key : ∀ (L : Ideal A) [L.IsHopfIdeal k], L ≤ I ⊔ J → ∀ y ∈ L,
        TensorProduct.map K.mkQ K.mkQ (comul (R := k) y) = 0 := by
      intro L _ hL y hy
      have hle : L.restrictScalars k ≤ K := fun a ha => hL ha
      have e : K.mkQ = (Submodule.mapQ (L.restrictScalars k) K LinearMap.id hle) ∘ₗ
          (L.restrictScalars k).mkQ := by
        rw [Submodule.mapQ_mkQ, LinearMap.comp_id]
      rw [e, TensorProduct.map_comp, LinearMap.comp_apply,
        Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := L.restrictScalars k) hy, map_zero]
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, map_add, key I le_sup_left y hy, key J le_sup_right z hz, add_zero]
  antipode_mem x hx := by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (Ideal.IsHopfIdeal.antipode_mem (R := k) hy)
      (Ideal.IsHopfIdeal.antipode_mem (R := k) hz)

theorem exists_quotient_kerIdeal_sup_frobKerIdeal : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra k C) (_ : IsCocomm k C) (_ : Module.Finite k C) (π : G.A 1 →ₐc[k] C), Function.Surjective π ∧ RingHom.ker π = kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) ∧ (∀ a ∈ augIdeal k C, a ^ p = 0) ∧ frobKerIdeal p k (G.A 1) ≤ augIdeal k (G.A 1) ^ 2 := by
  intro p _ k _ _ G H q
  haveI : (kerIdeal (q.app 1)).IsHopfIdeal k := isHopfIdeal_kerIdeal_of_bialgHom k _ _ (q.app 1)
  haveI : (frobKerIdeal p k (G.A 1)).IsHopfIdeal k := FrobKerOrder.isHopfIdeal p k (G.A 1)
  set I := kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) with hI
  haveI : I.IsHopfIdeal k := isHopfIdeal_sup _ _
  let π : G.A 1 →ₐc[k] G.A 1 ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : Module.Finite k (G.A 1) := G.finite 1
  refine ⟨G.A 1 ⧸ I, inferInstance, inferInstance, KerGrp.isCocomm_of_surjective π hπ,
    Module.Finite.of_surjective (π : G.A 1 →ₗ[k] G.A 1 ⧸ I) hπ, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem, ?_, FrobKerOrder.le_sq p k (G.A 1)⟩
  intro a ha
  obtain ⟨b, rfl⟩ := hπ a
  have hb : b ∈ augIdeal k (G.A 1) := ha
  change Ideal.Quotient.mk I b ^ p = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (pow_mem_frobKerIdeal hb)

end GlobalTheory.PDiv.FrobKerInter

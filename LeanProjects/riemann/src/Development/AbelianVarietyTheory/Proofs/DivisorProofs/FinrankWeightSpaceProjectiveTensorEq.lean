import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLocalOfCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceIffIdempotentFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotOneSubIdempotentEqMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceTopEqKerSmulStatement
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.WtRank

abbrev chr (k : Type) [Field k] (C : Type) [CommRing C] (χ : C →+* k) : k ⊗[ℤ] C →ₐ[k] k :=
  Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem finrank_fix {k A M : Type*} [Field k] [CommRing A] [Algebra k A] [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] (e : A) (W : Submodule k M)
    (hW : ∀ m, m ∈ W ↔ e • m = m) :
    Module.finrank k W = Module.finrank k (M ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A M)) := by
  set f : M →ₗ[k] M := DistribSMul.toLinearMap k M (1 - e)
  have hker : W = LinearMap.ker f := by
    ext m
    rw [hW, LinearMap.mem_ker]
    simp only [f, DistribSMul.toLinearMap_apply, sub_smul, one_smul, sub_eq_zero, eq_comm]
  have hrange : (Ideal.span {1 - e} • ⊤ : Submodule A M).restrictScalars k = LinearMap.range f := by
    ext m
    rw [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul, LinearMap.mem_range,
      Submodule.mem_smul_pointwise_iff_exists]
    simp [f]
  have e1 := (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {1 - e} • ⊤ : Submodule A M)).finrank_eq
  rw [← e1, hrange, hker]
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  omega

theorem weight_finrank_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ H _ _ _ σ
  letI inst : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift
    (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom
  intro hP χ
  have hP' : Module.Projective (k ⊗[ℤ] C) H := hP
  have hact : ∀ (a : k ⊗[ℤ] C) (h : H), a • h = (Algebra.TensorProduct.lift
      (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)) a h := fun _ _ => rfl
  haveI : IsScalarTower k (k ⊗[ℤ] C) H := ⟨fun l a h => by
    rw [hact, hact, map_smul, LinearMap.smul_apply]⟩
  obtain ⟨e, he, h1, hn⟩ := GlobalTheory.T.exists_idempotent_local_of_character k (k ⊗[ℤ] C) (chr k C χ)
  have hσ : ∀ c, σ c = DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext h
    rw [DistribSMul.toLinearMap_apply, hact]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hlm : ∀ c, ((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c =
      DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext x
    simp [Algebra.TensorProduct.includeRight_apply]
  have eH : (⨅ c : C, (σ c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hσ]
  have eA : (⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hlm]
  rw [eH, eA]
  rw [finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C H χ e he h1 hn), finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C (k ⊗[ℤ] C) χ e he h1 hn),
    GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul k (k ⊗[ℤ] C) (chr k C χ) e he h1 hn H]
  have hq : Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) =
      Module.finrank k (H ⧸ (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H)) := by
    have heq : GlobalTheory.HTRho.mSub σ χ ⊤ = (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H).restrictScalars k := by
      ext x; rw [Submodule.restrictScalars_mem]; exact GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul k C H σ χ x
    rw [heq]; exact (Submodule.Quotient.restrictScalarsEquiv k _).finrank_eq
  rw [hq]
  congr 1
  have hI : (Ideal.span {1 - e} • ⊤ : Submodule (k ⊗[ℤ] C) (k ⊗[ℤ] C)) = Ideal.span {1 - e} := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact ((Submodule.quotEquivOfEq _ _ hI).restrictScalars k).finrank_eq.symm

end GlobalTheory.WtRank

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslCoactionFreeCoassocCounital
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem mulP_flat : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ),
    RingHom.Flat ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n
  obtain ⟨hassoc, hcounit, hsurj⟩ := G.transl_free n
  obtain ⟨-, -, hff, -⟩ := GlobalTheory.HopfQuot.finite_faithfullyFlat_ker (G.transl n) hassoc hcounit hsurj
  set B₀ := AlgHom.equalizer (G.transl n)
    (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) with hB₀
  let f : G.A n →ₐ[R] B₀ := AlgHom.codRestrict (G.mulP n : G.A n →ₐ[R] G.A (n + 1)) B₀
    (fun a => by
      show G.transl n (G.mulP n a) = G.mulP n a ⊗ₜ[R] 1
      exact G.transl_mulP n a)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Test.mulP_injective G n (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨e, he⟩ := G.exists_mulP_eq_of_transl_eq n y.1 y.2
    exact ⟨e, Subtype.ext he⟩
  have h1 : RingHom.Flat (algebraMap B₀ (G.A (n + 1))) := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have h2 : RingHom.Flat (f : G.A n →+* B₀) := RingHom.Flat.of_bijective hf
  have h3 := RingHom.Flat.comp h2 h1
  convert h3 using 1
  exact RingHom.ext fun a => rfl
end GlobalTheory.PDivGroup

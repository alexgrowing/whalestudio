import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverBaseChangeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem one_tmul_injective_field (K L M : Type) [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    Function.Injective (fun m : M ↦ (1 : L) ⊗ₜ[K] m) := by
  have h1 : Function.Injective ((Algebra.linearMap K L).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
  have h2 : (fun m : M ↦ (1 : L) ⊗ₜ[K] m) = ((Algebra.linearMap K L).rTensor M) ∘ (TensorProduct.lid K M).symm := by
    funext m; simp
  rw [h2]; exact h1.comp (TensorProduct.lid K M).symm.injective

theorem pullHO_injective_field (K L : Type) [Field K] [Field L] [Algebra K L] (X X' : Scheme.{0}) (s : X ⟶ Sp K)
    (s' : X' ⟶ Sp L) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap K L))) (hs : IsSeparated s)
    (hq : QuasiCompact s) :
    Function.Injective (pullHO1 h.w) ∧ Function.Injective (pullHO2 h.w) := by
  obtain ⟨⟨e1, he1⟩, ⟨e2, he2⟩⟩ := GlobalTheory.T.structure_cohomology_flat_base_change K L X X' s s' φ h hs hq
  refine ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_⟩
  · apply one_tmul_injective_field K L
    apply e1.injective
    simp only [he1, hab]
  · apply one_tmul_injective_field K L
    apply e2.injective
    simp only [he2, hab]

theorem noPrimO2_axesO1_descend : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  intro K L _ _ _ A _ B _ φ hφ hA
  have hpA : IsProper A.hom := hA.proper
  have hpAA : IsProper (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨Φ, hΦ, hμ, hf, hs, ha1, ha2⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback K L (algebraMap K L) A B φ hφ
  have injA := pullHO_injective_field K L A.left B.left A.hom B.hom φ hφ.1 inferInstance inferInstance
  have injAA := pullHO_injective_field K L (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom Φ hΦ
    inferInstance inferInstance
  have N := pull_over_baseChange_comm K L (algebraMap K L)
  refine ⟨fun hB z hz ↦ ?_, fun hB y h1 h2 ↦ ?_⟩
  · apply injA.2
    rw [map_zero]
    apply hB
    have e := congrArg (pullHO2 hΦ.w) hz
    rw [map_add] at e
    rw [← (N A (A ⊗ A) B (B ⊗ B) μ[A] μ[B] φ Φ hφ.1.w hΦ.w hμ).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (fst A A) (fst B B) φ Φ hφ.1.w hΦ.w hf).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (snd A A) (snd B B) φ Φ hφ.1.w hΦ.w hs).2]
    exact e
  · apply injAA.1
    rw [map_zero]
    apply hB
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha1).1, h1, map_zero]
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha2).1, h2, map_zero]

end GlobalTheory.AbCoh

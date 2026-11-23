import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionModuleExtendingResidueMaps
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
open CategoryTheory GlobalTheory.SelFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_module_extending_residue_maps : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] (P : Type) [AddCommGroup P] [Module Λ P] [Module.Finite Λ P] (N : Submodule Λ P),
  ∃ (B : ModuleCat.{0} Λ) (f : IsLocalRing.ResidueField Λ →ₗ[Λ] B), Tors Λ B ∧ Function.Injective f ∧
    ∀ φ : N →ₗ[Λ] IsLocalRing.ResidueField Λ, ∃ u : P →ₗ[Λ] B, u ∘ₗ N.subtype = f ∘ₗ φ := by
  first | exact @GlobalTheory.SelFun.exists_torsion_extension | exact GlobalTheory.SelFun.exists_torsion_extension | (intros; apply GlobalTheory.SelFun.exists_torsion_extension <;> assumption)

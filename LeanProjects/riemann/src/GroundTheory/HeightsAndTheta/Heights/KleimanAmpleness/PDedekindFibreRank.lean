import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDedekindFibreRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Module TensorProduct

theorem DedekindFibreRank.proof : DedekindFibreRank.Statement := by
  intro S _ _ G _ _ hfin htf 𝔪 h𝔪
  have : Module.Flat S G := inferInstance
  let e₁ : (S ⧸ 𝔪) ≃ₐ[S] 𝔪.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom S (S ⧸ 𝔪) 𝔪.ResidueField)
      𝔪.bijective_algebraMap_quotient_residueField
  let e : (G ⧸ 𝔪 • (⊤ : Submodule S G)) ≃ₗ[S] 𝔪.Fiber G :=
    (TensorProduct.quotTensorEquivQuotSMul G 𝔪).symm ≪≫ₗ
      TensorProduct.congr e₁.toLinearEquiv (LinearEquiv.refl S G)
  rw [e.length_eq, Module.length_eq_of_surjective (R := 𝔪.ResidueField)
    𝔪.algebraMap_residueField_surjective, Module.length_eq_finrank, Ideal.finrank_fiber_eq_finrank]

end GroundTheory.Heights₂.Heights.Kleiman

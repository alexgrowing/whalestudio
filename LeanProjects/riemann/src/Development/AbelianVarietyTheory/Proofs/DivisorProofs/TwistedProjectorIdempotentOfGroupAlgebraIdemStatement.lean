import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorIdempotentOfGroupAlgebraIdem
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedProjector_idempotent_of_groupAlgebra_idem : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) → A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  first | exact @GlobalTheory.eOp_comp_self_of_conv_idem | exact GlobalTheory.eOp_comp_self_of_conv_idem | (intros; apply GlobalTheory.eOp_comp_self_of_conv_idem <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtaleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHomStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLiftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnitStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProperStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentialsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtensionStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem lemmaBT_holds : LemmaBT := by
  unfold GlobalTheory.CompanionTheory.Ar.BT.LemmaBT
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i hi hG
  refine ⟨GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ, ?_,
    fun hN => GlobalTheory.T.btOrder_eq_top_of_etale R T Γ
      (GlobalTheory.T.torsion_group_etale_of_unit R T Γ S G x N i hi hG hN), ?_, ?_,
    fun L _ _ M => GlobalTheory.T.exists_dual_to_invariant_differentials R T Γ S G x N i hi hG L M⟩
  · obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding R T Γ
    obtain ⟨hoi, htr⟩ := GlobalTheory.T.btOrder_embedding_open_immersion R T Γ j hj
    refine ⟨j, hj, hoi, htr, fun hP => ?_⟩
    exact GlobalTheory.T.btOrder_embedding_iso_finite R T Γ j hj
      (GlobalTheory.T.torsion_group_finite_of_proper R T Γ S G x N i hi hP)
  · intro a _ α hα f hf
    obtain ⟨a', _, ha'⟩ := GlobalTheory.T.torsion_group_endomorphism_lift R T Γ S G x N i hi a
    refine GlobalTheory.T.btOrder_comap_hom R T Γ T Γ a' α (fun t => ?_) f hf
    obtain ⟨_, _, hcancel, _⟩ := hi
    apply hcancel
    rw [Over.comp_left, Category.assoc, ha', hα t]
  · intro R' _ _ _ Γ' F hF
    obtain ⟨hd, hΓ'⟩ :=
      GlobalTheory.T.btOrder_base_change_generic R T Γ R' Γ' F hF
    obtain ⟨-, e, he⟩ := GlobalTheory.T.hopf_order_scalar_extension R T R' _
      (GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ) hd
    rw [hΓ']
    exact ⟨e, he⟩

end GlobalTheory.CompanionTheory.Ar.BT

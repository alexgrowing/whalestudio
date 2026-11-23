import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExistsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjSplitLocalModelBySupportedPairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilVacuumLocalModelIntegralMatrixPairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearLawLocalModelMulClosedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearLawLocalModelInvStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalComponentsOneMulInvStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLocalSupportedScalarComponentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsScalarPreservesIntegralMatricesSubstStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocOm

theorem omLoc : ∀ (D : D7), OmLoc D := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW μS μT hμS hμT Y Y' _ _ _ _ FS FT Tm hTm g gk h hk hg hh Φ Φ' hΦ'
  have U := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k p Y Y' S T FS FT ψ hW.std).1
  have enl : ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → Enl gk hk →
      LawLoc ω μS μT Tm g gk h hk := by
    intro g gk h hk hg hh he
    obtain ⟨T₂, hT₂, hT₂e⟩ := GlobalTheory.T.conj_splitLocalModel_by_supported_pair D k p ψ S T χS χT ω hW μS μT Y Y' FS FT Tm hTm g gk h hk hg hh
    obtain ⟨Φ₀, Φ₀', h0, h0', hv⟩ := GlobalTheory.T.weil_vacuum_local_model_integral_matrix_pair D k p ψ S T χS χT ω hW μS μT hμS hμT Y Y' FS FT Tm hTm g gk h hk hg hh he
    have inv1 : ∀ F, ω (g⁻¹, h⁻¹) (ω (g, h) F) = F := fun F => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have inv2 : ∀ F, ω (g, h) (ω (g⁻¹, h⁻¹) F) = F := fun F => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hT : T₂ = Tm := U T₂ Tm hT₂ hTm Φ₀ h0 (by rw [hT₂e Φ₀ Φ₀' h0', ← hv, inv1])
    intro Φ Φ' hΦ'
    have := hT₂e Φ Φ' hΦ'
    rw [hT] at this
    rw [this, inv2]
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_scalar_preservesIntegralMatricesSubst k Y Y' gk hk
  obtain ⟨zk, hzk⟩ : ∃ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) :=
    ⟨Units.map (Matrix.scalar Y : k →+* Matrix Y Y k).toMonoidHom c, by
      simp [Matrix.smul_one_eq_diagonal]⟩
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_splitLocal_supported_scalar_component D k p T Y FT c zk hzk
  have iS := GlobalTheory.T.splitLocalComponents_one_mul_inv D k p S Y' FS
  have iT := GlobalTheory.T.splitLocalComponents_one_mul_inv D k p T Y FT
  have l1 := enl g gk (h * z⁻¹) (hk * zk⁻¹) hg (iT.2.1 _ _ _ _ hh (iT.2.2 _ _ hz)) (hc zk hzk).1
  have l2 := enl 1 1 z⁻¹ zk⁻¹ iS.1 (iT.2.2 _ _ hz) (hc zk hzk).2
  have l3 := GlobalTheory.T.linearLaw_localModel_mul_closed D k S T ω μS μT Y Y' Tm _ _ _ _ _ _ _ _ l1 (GlobalTheory.T.linearLaw_localModel_inv D k S T ω μS μT Y Y' Tm _ _ _ _ l2)
  simp only [inv_one, mul_one, inv_inv, inv_mul_cancel_right] at l3
  exact l3 Φ Φ' hΦ'

end GlobalTheory.LocOm

end

import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProductStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegLDual

theorem lSegDual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegDual k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ
  obtain ⟨hd, hco⟩ := id hπ
  have hsm : IsSmooth π := hco.isSubquotient.isSmooth (isSmooth_prodIrr _ hd)
  obtain ⟨hirr, f, hf, -⟩ := hco
  have hci : (contra π).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N) (hA k N V π hsm hirr) hirr
  obtain ⟨hd', ⟨e⟩⟩ := GlobalTheory.T.contragredient_segment_product_equiv hA Δ hd
  have hinj : Function.Injective (GlobalTheory.ContraRefl.contraMap f) := fun a b h => Subtype.ext (LinearMap.ext fun v => by
    obtain ⟨w, rfl⟩ := hf v
    exact LinearMap.congr_fun (congrArg Subtype.val h) w)
  exact GlobalTheory.T.irreducible_sub_segment_product hA hZ (segDual Δ) hd' (contra π) (isSmooth_smoothRep _) hci
    (e.toIntertwiningMap.comp (GlobalTheory.ContraRefl.contraMap f))
    (e.toLinearEquiv.injective.comp hinj)

end GlobalTheory.CompanionTheory.SegLDual

end

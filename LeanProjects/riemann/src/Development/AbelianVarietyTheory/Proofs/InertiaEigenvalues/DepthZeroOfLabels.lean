import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterTame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualOfLabelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaUnipotentDepthZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroTame

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL)
    (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf →
    DepthZ D := by
  intro hP hW hS hL D P hrow hlab hchi
  obtain ⟨S, hT, hLaws, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hP.fin hL D P hrow
  have hfix : ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k),
      TameLP D (D.naut.locV i PI (D.naut.plGw k v)) := by
    intro i PI k v
    have hw := GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
    have htame := GlobalTheory.PendOf.isTame_mu_plGw hL D P S hT i k v hw
    have hTB := GlobalTheory.T.tame_block_type_at_split_place hL D P S hT i _ hw ⟨k, D.naut.plGw_over k v⟩ htame
    obtain ⟨x, hx0, hx⟩ := hTB.2 PI
    have hfixd : x ∈ GlobalTheory.PRep.fixed ((S i _ hw).rep PI).π
        (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin (D.R.r + D.R.t))) := by
      intro h
      have h' : ((S i _ hw).rep PI).π h x = x := GlobalTheory.JacBlock.KOne_le_stab htame hx h.2
      simpa using h'
    have hwild := GlobalTheory.DepthZeroLoc.main hP.bz hW hS hL D _ _ ((S i _ hw).rep PI) ⟨x, hfixd, hx0⟩
    intro σ hσI hσW
    have hd : D.naut.lpDim (D.naut.locV i PI (D.naut.plGw k v)) = D.R.r + D.R.t := by
      rw [← P.T.dim, (S i _ hw).locV PI, (hLaws i _ hw).dim]
    rw [P.T.inePol _ _ σ hσI, (S i _ hw).locV PI, hT.rc i _ hw, hwild σ hσW, hd]
  intro i PI k w hw
  obtain ⟨v, rfl | hc⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · exact hfix i PI k v
  · exact ((GlobalTheory.T.conj_dual_of_labels hP hL D P hlab) i PI k v w hc).2.1 (hfix i PI k v)

end GlobalTheory.DepthZeroTame

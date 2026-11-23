import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcSplit

theorem locV_unr_frobEig_of_hasSatake : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ → GlobalTheory.SmGL.HasSatake σ.ρ α → D.naut.unr (D.naut.locV i Q sp.w) ∧ D.naut.frobEig (D.naut.locV i Q sp.w) = Finset.univ.val.map (fun k => (((α k)⁻¹ : ℂˣ) : ℂ)) := by
  intro hL D P i Q sp σ α hS hα
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hS
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w,
    GlobalTheory.CuspRep.ParLaws.rec_eq_diag (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 sp.w)) hα] at h3
  have hu : D.naut.unr (D.naut.locV i Q sp.w) :=
    (P.T.unr _ _).2 (by rw [h3]; exact (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _))
  refine ⟨hu, ?_⟩
  rw [P.T.frobEig _ _ hu, h3, GlobalTheory.WeilDeligne.WD.frobEig_diag]

end GlobalTheory.LlcSplit

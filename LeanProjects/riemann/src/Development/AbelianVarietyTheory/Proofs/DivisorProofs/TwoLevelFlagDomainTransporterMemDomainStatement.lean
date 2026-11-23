import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainTransporterMemDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelFlagDomain_transporter_mem_domain : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom := by
  first | exact @GlobalTheory.TwoLevelsDom.lact_tr_mem_dom | exact GlobalTheory.TwoLevelsDom.lact_tr_mem_dom | (intros; apply GlobalTheory.TwoLevelsDom.lact_tr_mem_dom <;> assumption)

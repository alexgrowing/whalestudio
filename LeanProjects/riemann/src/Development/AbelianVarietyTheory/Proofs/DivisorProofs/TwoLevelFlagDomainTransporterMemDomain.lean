import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom

set_option autoImplicit false

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

namespace GlobalTheory.TwoLevelsDom

theorem lact_tr_mem_dom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom :=
  fun M g c _x hx => GlobalTheory.CuspEmb.lact_tr_mem M g c hx

end GlobalTheory.TwoLevelsDom

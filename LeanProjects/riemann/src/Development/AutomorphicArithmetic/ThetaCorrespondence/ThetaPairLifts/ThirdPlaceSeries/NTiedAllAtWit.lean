import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NTiedAllAtWit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem exists_core_parameters_agree : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), ∃ (I : TwIn (q.w.D q.Z)) (n : _root_.Formalism.L2.NTiedAllAlt (q.w.D q.Z) q.O.ex.nch I), I.E = twEOf q.O.ex.xd ∧ DQ.GoodAllAt (q.w.D q.Z) q.O.ex.nch I ∧ (⟨n.cf, n.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = ⟨TC.cf q.w.I q.w.l q.Z, q.x.n.tp⟩ ∧ n.gal = q.core_data_of_point.a.all.gal ∧ n.n = q.core_data_of_point.a.all.n ∧ n.exp = q.core_data_of_point.a.all.exp ∧ n.chiD = q.core_data_of_point.a.all.chiD ∧ n.twF = q.core_data_of_point.a.all.twF ∧ HEq n.types q.core_data_of_point.a.all.types ∧ HEq n.cover q.core_data_of_point.a.all.cover ∧ n.plB = q.core_data_of_point.a.all.plB := by
  intro hL p K q
  obtain ⟨I, hE, hG, hC⟩ := q.x.good.tw
  have hch := q.core_data_of_point.a.chr_eq
  have hc : Formalism.L2.NChoiceTied (q.w.D q.Z) q.O.ex.nch I (Formalism.L2.avDesign (q.w.D q.Z)) := by
    have c := q.core_data_of_point.a.all.choice
    first
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              good := fun w hw h => hC w hw h, conj := c.conj }
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              conj := c.conj }
  refine ⟨I, { q.core_data_of_point.a.all with choice := hc }, hE, hG, hch, rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, rfl⟩
end GlobalTheory.Mem.Top.Bl
end
end

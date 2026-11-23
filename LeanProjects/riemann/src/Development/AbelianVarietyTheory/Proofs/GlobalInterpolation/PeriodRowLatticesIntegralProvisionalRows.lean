import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTrueColsRowInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherProperties

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.RowIntQ

theorem rowVal_of_sameForm {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (hX : B.fields.Ok) (u : B.Word) (a : I.ι)
    (x : Formalism.L2.Col.MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps)
    (hx : x ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) (G : (I.per l u a).Mt)
    (hG : GlobalTheory.Mem.Df.SameForm I l u a (GlobalTheory.Mem.Df.toCx I hX a x) G) : GlobalTheory.PerQ.RowVal I l u a G := by
  intro c
  obtain ⟨y, hy, e⟩ := GlobalTheory.PerQ.RowIntModel.mtildeL_rep_mem (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps x hx c
  refine ⟨y, hy, ?_⟩
  rw [e]
  exact hG ((I.stX a).rep c)

theorem rowInt_of_sameForm : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (hX : B.fields.Ok) (e : ∀ a : (I.cols l).Tup, GlobalTheory.Mem.Df.MtCx I a ≃ₗ[ℂ] Z.W.Amb a),
    (∀ u F, GlobalTheory.Mem.Df.SameForm I l u I.mu0 F ((Z.W.eMt0 u).symm (e (I.cols l).mu0 F))) →
    (∀ u (a : (I.cols l).Tup) F, GlobalTheory.Mem.Df.SameForm I l u a F ((Z.W.eMtTw u a).symm (e a F))) →
    (∀ (a : (I.cols l).Tup), ∀ F ∈ (Z.W.Mtilde a).carrier, ∃ x ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps,
      F = e a (GlobalTheory.Mem.Df.toCx I hX a x)) → GlobalTheory.PerQ.RowInt I l Z := by
  intro B X I _ l Z hX e h0 htw hlat
  refine ⟨fun u F hF => ?_, fun u a F hF => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hlat _ F hF
    exact rowVal_of_sameForm I l hX u _ x hx _ (h0 u _)
  · obtain ⟨x, hx, rfl⟩ := hlat _ F hF
    exact rowVal_of_sameForm I l hX u _ x hx _ (htw u _ _)

theorem rowInt_over : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), ∀ o : P.q.Over,
    GlobalTheory.PerQ.RowInt w.I w.l o.Z := by
  intro K B f T w P o
  refine rowInt_of_sameForm w.I w.ok w.l o.Z P.hX P.q.per.e P.q.per.ref P.q.per.tw ?_
  intro a F hF
  classical
  obtain ⟨hg, hiff⟩ := (P.q.t.tA true a).latT
  obtain ⟨c, rfl⟩ := hF
  choose! g hgy using hg
  let n := (GlobalTheory.Mem.R3.Rw.mAU (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr true a).n
  let y : Fin n → B.LL := ∑ v ∈ (P.q.p.sA true a).lat.gen, B.OtoLL (c v) • @id (Fin n → B.LL) (g v)
  have hjy : (P.q.t.tA true a).j y = ∑ v ∈ (P.q.p.sA true a).lat.gen, B.embLL ((⟨B.OtoLL (c v), B.O_int (c v)⟩ : 𝓞 B.LL) : B.LL) • v := by
    refine (map_sum (P.q.t.tA true a).j _ _).trans (Finset.sum_congr rfl fun v hv => ?_)
    exact ((P.q.t.tA true a).j.map_smulₛₗ _ _).trans (congrArg _ (hgy v hv))
  obtain ⟨x, hx, hj⟩ := P.q.per.crd a y
  refine ⟨x, (GlobalTheory.AtG.RX.isFormOf_mem_iff (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr a hx).1 ((hiff y).2 ⟨fun v => ⟨B.OtoLL (c v), B.O_int (c v)⟩, hjy⟩), ?_⟩
  exact hjy.symm.trans hj

end GlobalTheory.RowIntQ

end

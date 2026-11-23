import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem pathConv_zip_fock (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ (φ d : PureT G p), VecAll ρ e p φ d →
      ∀ (P' : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      PathConv W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F ∧
      IsCuspListed W.θ Y (liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F)
  | _, .nil, _, _, _, _, _, _, hF => ⟨trivial, hF⟩
  | _, .snoc a p, hg, φ, d, hv, P', F, hF => by
    have hg' : OnGrid D.R.m t p := fun b hb => hg b (List.mem_append_left [a] hb)
    have ha : IsGridArrow D.R.m t a := hg a (List.mem_append_right p.arrows (List.mem_singleton_self a))
    obtain ⟨h1, h2⟩ := pathConv_zip_fock M ρ t he hC p hg' φ.1 d.1 hv.1 P'.1 F hF
    obtain ⟨h3, h4⟩ := hC a ha e he φ.2 d.2 hv.2 P'.2 _ h2
    exact ⟨⟨h1, h3⟩, h4⟩

theorem mem_support_tensT {X Y : Node} {p : Path T X Y} (τi : PolT G p →₀ ℂ) (τf : TotT G p) (x : PureT G p)
    (hx : x ∈ (tensT W τi τf).support) :
    ∃ d ∈ τf.support, ∃ P' : PolT G p, x = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P' := by
  classical
  unfold tensT at hx
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hx)
  obtain ⟨d, hd, hx'⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d, hd, P, Finset.mem_singleton.1 (Finsupp.support_single_subset hx')⟩

theorem totConv_tensE : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ : TotT G p) (φ : PureT G p → PureT G p), (∀ d ∈ τ.support, GlobalTheory.FlipRun.VecAll ρ e p (φ d) d) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, TotConv W M p (GlobalTheory.FlipRun.tensE W p Q τ) F := by
  intro D T L sc G W M ρ t e he hC X Y p hg τ φ hv F hF Q x hx
  obtain ⟨d, hd, P', rfl⟩ := mem_support_tensT _ τ x hx
  exact (pathConv_zip_fock M ρ t he hC p hg (φ d) d (hv d hd) P' F hF).1

end GlobalTheory.FlipRun

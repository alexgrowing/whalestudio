import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
variable (Y : Cov p i)
def RowsTAlt : Prop := p.PointConditions' ∧ RecTied D L
def EventuallyAtAllPoints {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p : Pt Fm x hx ι), _root_.GlobalTheory.CovTop.RowsTAlt p → Q x hx ι p
theorem EventuallyAtAllPoints.and {eps : ℝ} {Fm : FamP eps} {Q Q' : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x), Pt Fm x hx ι → Prop}
    (h : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm Q) (h' : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm Q') : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x hx ι p => Q x hx ι p ∧ Q' x hx ι p := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  exact ⟨max a b, fun x hx hle ι p hp =>
    ⟨h x hx ((le_max_left _ _).trans hle) ι p hp, h' x hx ((le_max_right _ _).trans hle) ι p hp⟩⟩
def LiftsCondition (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (PP C : ℝ), Prop) : Prop :=
  Closed FamHyp fun Fm _ => ∃ C : ℝ, 0 ≤ C ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x hx ι p => ∀ i, Q Fm x hx ι p i (Fm.parT x hx ι).PP C
def CoversCondition (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
    (_Y : Cov p i) (PP C : ℝ), Prop) : Prop :=
  _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x hx ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    ∀ Y : Cov p i, GoodCov p i Y → Q Fm x hx ι p i Y PP C
def GramCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => GramAt p i
def LiftRecursive : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => RecAt p i
def LiftTruncation : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => CutAt p i
def LiftBadSet : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => BadAt p i
def LiftLambdaBound : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => LamAt p i C
def SizeCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i PP C => SizeAt p i PP C
def MeasureCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => MeasAt p i C
def LiftRational : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ _ => RatAt p i
def CoreBound' : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => CoreAt p i C
def LiftLowBound : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => LowAt p i C
def AnchorCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i _ C => AnchorAt p i C
def LowDefectCondition : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → LowAt p i C
def DeepExistence : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 < (Fm.D x ι).R.m →
  ∃ Y : Cov p i, GoodCov p i Y
def DeepGoodness : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => DeepGoodAt p i Y
def RingCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => RingAt p i Y
def MapsCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => MapsAt p i Y
def CoverRank : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => RkAt p i Y PP
def MinimalGenerator : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => GminAt p i Y PP
def FlatDegreeCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => FlatDegAt p i Y
def FlatnessCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ C => FlatAt p i Y C
def UniformLowerBound : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ C => UAt p i Y C
def SumBoundCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y _ _ => SumAt p i Y
def CoverDegree : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → DegAt p i Y u1
def ShareCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → ShareAt p i Y PP u1
def HeightCondition : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HeightAt p i Y PP C u1
def CoverHeightSum : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → HSAt p i Y PP C u1
def CovolumeBoundOfX : Prop := Closed FamHyp fun Fm CH =>
  ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)
def _root_.GlobalTheory.BigTop.CovolumeBound : Prop := Closed FamHyp fun Fm CH =>
  ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)
end GlobalTheory.CovTop
end
end

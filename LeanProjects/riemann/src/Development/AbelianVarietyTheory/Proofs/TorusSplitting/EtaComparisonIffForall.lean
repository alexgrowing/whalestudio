import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.I2AtFramePointsAlpha
import Development.AbelianVarietyTheory.BlockTheory.ArchimedeanEta.EtaleProductAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.DifferentiableConjConj
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.SemicharUnitFrame
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EtaProductOfTorusBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusConditionWithW0OfPins

noncomputable section

namespace GlobalTheory.EtaPinnedCompare

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
  GlobalTheory.TorusFrameRigid GlobalTheory.EtaProdCompare
open ReciprocityTheory.ChartRestriction.G.I2 (TorusAt Vsp Hf PT)
open scoped ComplexConjugate

section Pins

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

def conjPer (W : UnfAt U k x) : Submodule ℂ ((W.F.Di (W.ik k)).La → ℂ) :=
  Submodule.span ℂ (Set.range fun (j : Fin W.g) a => star (W.Pm a j))

theorem theta_entire {W : UnfAt U k x} (Wu : UnitAt W) : Differentiable ℂ Wu.θ := by
  have hF : GlobalTheory.EtaAn.AHFrame W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr :=
    ⟨Wu.herm, Wu.pos, Wu.c1, Wu.c2, Wu.c3, Wu.c4, fun j hj => by rw [← W.pt]; exact Wu.c5 j hj, Wu.c6⟩
  have key : ∀ y (_ : y = W.F.u (W.ik k) W.Pm) (s : Semi.LB.Sec (PPx y)),
      GlobalTheory.EtaAn.IsFnOf W.F (W.ik k) W.Pm Wu.fr y s Wu.θ → Differentiable ℂ Wu.θ := by
    intro y hy s hs
    subst hy
    exact (GlobalTheory.EtaAn.isFnOf_entire_factor E H Dw l Xo _ _ _ W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr W.per hF s Wu.θ hs).1
  exact key _ W.pt (U.un k x).s Wu.c7

end Pins

section Bound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Z : FD.Data E r} {x : FD.Frame Z.Ψ r}

end Bound

section Record

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D}

def EtaComparisonAt (h : LawsP T) (tableLineDegreeTwo : ℝ) (j i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (DF m r1 Nc nt : ℕ)
    (R0 : ℝ) : Prop :=
  2 ≤ r1 → EtNum D.host.E D.R.r T.Q.l.M m r1 Nc nt tableLineDegreeTwo → EtParRun T j DF T.Q.l.M m R0 →
    IndefiniteRowSideFullHecke.EtaleProductIsoRefl.EtProdA h r1 Nc nt j i η →
    ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : FD.Frame ((T.U j σ).X k).Ψ D.R.r),
      x ∈ ((T.U j σ).X k).dom →
      recNrm (T.U j σ) (xiR D) (wtA (wEt D j i)) (wEt D j i).n η.1 k x ≤
        Real.exp (-(i : ℝ) * (I2.phiFD ((T.U j σ).X k) (I2.th (E := D.host.E) T.Q.l.M R0) x - tableLineDegreeTwo))

end Record

end GlobalTheory.EtaPinnedCompare

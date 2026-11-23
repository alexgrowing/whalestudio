import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
import Formalism.LocalToGlobal.HermitianColumns.HermCols

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  {S : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad}

def DetTie.Pinned (Hh : Formalism.L2.Herm.HermTied D) (Y : DetTie S) : Prop :=
  ∀ (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det (y : GL (Fin 1) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) =
      Matrix.GeneralLinearGroup.det (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    Y.dt x = Hh.dt y

theorem DetTie.Pinned.eq {Hh : Formalism.L2.Herm.HermTied D} {Y Y' : DetTie S} (h : Y.Pinned Hh) (h' : Y'.Pinned Hh)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hy : Matrix.GeneralLinearGroup.det (y : GL (Fin 1) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) =
      Matrix.GeneralLinearGroup.det (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :
    Y.dt x = Y'.dt x := (h x y hy).trans (h' x y hy).symm

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {G : GAtP p}

def StepIn.TwPinned (Hh : Formalism.L2.Herm.HermTied D) (St : StepIn M i hi G) : Prop :=
  ∀ β, ∃ Y : DetTie (St.K β).lev, Y.Pinned Hh ∧ St.tw β = DetTw.ofChiD Y (cTw D i)

end Formalism.MainNotions.G.CmpJ

end

import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
import Formalism.LocalToGlobal.LatticeGeometry.ViewsB
import Formalism.SharpRestriction.Divisibility.WeightAlgebra

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

def toWeightFamilies (F : ShimFam D G Lev) : WeightFamilies.Prov D := F.forms.toWeightFamilies

def ptCast (F : ShimFam D G Lev) {w w' : Dat D Lev} (e : w = w') (p : ℕ)
    (y : ((F.U w').pad.loc p).Pt ((F.U w').pad.loc p).YY) :
    ((F.U w).pad.loc p).Pt ((F.U w).pad.loc p).YY :=
  cast (congrArg (fun v => ((F.U v).pad.loc p).Pt ((F.U v).pad.loc p).YY) e.symm) y

def ptOfEx {r j p : ℕ} {L : ModuliIntegralCharts.Loc D r j p} (ex : ModuliIntegralCharts.ExtA D L) : L.Pt L.YY :=
  ex.yEta (Classical.choice (ex.genNe L.YY))

section PJ

variable (F : ShimFam D G Lev) (I : Type) (dat : I → Dat D Lev) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I)

abbrev PtMap (j : ℕ) : Type :=
  ∀ la, F.forms.Pt j la →
    ((F.U (dat (iW j))).pad.loc (WeightAlgebra.resCh la)).Pt ((F.U (dat (iW j))).pad.loc (WeightAlgebra.resCh la)).YY

def ptW (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j) (ptM : PtMap F I dat iW D.R.m)
    (j : ℕ) (h1 : 1 ≤ j) (hm : j ≤ D.R.m) : PtMap F I dat iW j :=
  if hj : j < D.R.m then fun la y => ptCast F (hiW j h1 hj) _ (F.forms.pt66 j la y)
  else cast (congrArg (fun k => PtMap F I dat iW k) (by omega : D.R.m = j)) ptM

def toPJ (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j) (ptM : PtMap F I dat iW D.R.m)
    (j : ℕ) (h1 : 1 ≤ j) (hm : j ≤ D.R.m) : WeightAlgebra.PJ D (toWeightFamilies F) (indefiniteDataFamily F.U I dat hI) j :=
  F.forms.mkPJ (indefiniteDataFamily F.U I dat hI) j (iW j)
    (fun hj => by
      show (dat (iW j)).N = D.R.r
      rw [hiW j h1 hj, datW_N])
    (fun hj => by
      show (dat (iW j)).j = (D.R.sigW j).1
      rw [hiW j h1 hj, datW_j D F.κg h1 hm])
    (ptW F I dat iW hiW ptM j h1 hm)

def toWeightAlgebra (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j) :
    WeightAlgebra.Prov D (toWeightFamilies F) (indefiniteDataFamily F.U I dat hI) :=
  fun j h1 hm => toPJ F I dat hI iW hiW
    (fun la _ => ptOfEx ((F.U (dat (iW D.R.m))).pad.ex (WeightAlgebra.resCh la))) j h1 hm

end PJ

def MjSat (F : ShimFam D G Lev) (j : ℕ) (volRec : ℝ) : Prop := F.forms.MjSat j volRec

theorem MjSat.forms {F : ShimFam D G Lev} {j : ℕ} {volRec : ℝ} (h : MjSat F j volRec) :
    F.forms.MjSat j volRec := h

def detWt {Tau : Type} [DecidableEq Tau] (N : ℕ) (τ : Tau) : Tau → Fin N → ℤ :=
  fun τ' _ => if τ' = τ then 1 else 0

def DeKey (F : ShimFam D G Lev) (j : ℕ) (ka : ℝ)
    (hm : ∀ (c : (F.U (datW D F.κg j)).Comp) (σ : D.what₂.LL →+* ℂ)
      (lam : D.what₂.Tau → Fin (datW D F.κg j).N → ℤ),
      G.Met ((F.U (datW D F.κg j)).alg.Yv c) σ ((F.U (datW D F.κg j)).alg.Lw c lam)) : Prop :=
  ∀ (σ : D.what₂.LL →+* ℂ) (w : WeightFamilies.Wt D j) (Fo : F.forms.Cusp j w),
    IsLUB (Set.range fun q : (Σ c : (F.U (datW D F.κg j)).Comp,
        G.pts ((F.U (datW D F.κg j)).alg.Yv c) σ) =>
      Real.exp ((w.n : ℝ) / 2 * ((D.R.f * D.R.r : ℕ) : ℝ) * ka) *
        Real.sqrt (G.pn _ σ _ (hm q.1 σ (wtOfN _ w)) (G.cx _ σ (F.forms.cmp j w q.1 Fo)) q.2))
      (F.forms.supN j w (σ.comp F.forms.kL) Fo)

end Formalism.L2.Geo

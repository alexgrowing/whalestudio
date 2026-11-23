import Formalism.LocalToGlobal.ProjectiveLattices.ResChPrime
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.DatIndep
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.DIV.Cons
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Top (D : D7) : Type 1 extends Core D where
  G : In66 Q
  nab : ∀ j, NabV (Q.Xo j) Q.c
  dδ : ∀ j n, DeltaDat (Q.Xo j) Q.c n

variable {D : D7}

def badN (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d * ∏ p ∈ D.host.levelPrimes, p

def wEt (D : D7) (j i : ℕ) : WeightFamilies.Wt D j :=
  WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)

structure LawsP (T : Top D) : Prop extends LawsCore T.toCore where

  allTest : ∀ j, InR D j → AllTest (T.Q.Xo j) T.Q.c

  reg : ∀ j, InR D j → regular₂ (T.Q.Xo j) T.Q.c (T.U j)

  datum_condition : T.G.PinDat
  tower : T.G.PinTower
  hasData_condition : T.G.HasData
  points_condition : T.G.PinPts
  lattice_condition : T.G.PinLat
  bc66 : T.G.BaseChange

  datIndep : ∀ j, 1 ≤ j → j < D.R.m → DatIndep (T.Q.Xo j) T.Q.c

  nabPin : ∀ j, InR D j → ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c (T.nab j)

  nabUniq : ∀ j, InR D j → NabUniq (T.Q.Xo j) T.Q.c

  thTot : ∀ j, InR D j → ThValTot (T.Q.Xo j) T.Q.c (T.nab j)
  thCusp : ∀ j, InR D j → ThInCusp (T.Q.Xo j) T.Q.c (T.nab j) (T.cuspA j)
  thNe : ∀ j, 1 ≤ j → j < D.R.m → ThNe0 (T.Q.Xo j) T.Q.c (T.nab j)

  kPsi : ∀ j, InR D j → KPsiIn (Dw := T.Q.Dw j) T.Q.c

structure LawsSh (T : Top D) : Prop where
  beta : ∀ j, InR D j → ∀ n, BetaExists (Dw := T.Q.Dw j) T.Q.c n (badN D)
  dLev : ∀ j, InR D j → ∀ n, (T.dδ j n).IsLev
  dNab : ∀ j, InR D j → ∀ n, ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).nab₂

  dPd : ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ∀ j, InR D j → ∀ n, (T.dδ j n).pd = p

  dPhi : ∀ j, InR D j → ∀ n, D.R.r ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ (T.dδ j n).PhiPin ph ψ x₀ ∧ (T.dδ j n).PsiTie ψ

  dRoot : ∀ j, InR D j → ∀ n, ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* (T.dδ j n).c₂.Fˣ)
    (gdet : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom) → Cls),
    CMP (T.Q.Xo j) T.Q.c (T.dδ j n) _ Cls δ gdet false
  shTot : ∀ j, InR D j → ∀ a n, Dom a n →
    ShortValTot (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)
  shCusp : ∀ j, InR D j → ∀ a n, Dom a n → LastPos (T.Q.Dw j) a →
    ShortInCusp (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.cuspA j) a n (T.dδ j n)
  shNe : ∀ j, 1 ≤ j → j < D.R.m → ShortNe0 (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.dδ j) (T.cuspA j)

def Packet66Rest (Q : Par D) : Prop :=
  ∃ G : In66 Q, G.PinDat ∧ G.PinTower ∧ G.HasData ∧ G.PinPts ∧ G.PinLat ∧ G.BaseChange

theorem LawsP.packet66_rest {T : Top D} (h : LawsP T) : Packet66Rest T.Q :=
  ⟨T.G, h.datum_condition, h.tower, h.hasData_condition, h.points_condition, h.lattice_condition, h.bc66⟩

def TopExists (D : D7) : Prop := ∃ T : Top D, LawsP T

end Formalism.L2.Pj

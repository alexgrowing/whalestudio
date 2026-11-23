import Formalism.LocalToGlobal.GlobalTheory.FamRows
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.LocalToGlobal.GlobalTheory.FamColP

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRows

open Formalism Formalism.HN Formalism.L2.Col Formalism.L2.Indef Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.GlobalTheoryTheory.FamCol

section Lemmas

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

def flD (C : ColObj K I) (u : I) : HeightOneSpectrum (𝓞 K) → ℤ := fun w => ⌊sgD C u w⌋

theorem flD_support_finite (C : ColObj K I) (u : I) : (Function.support (flD C u)).Finite := by
  classical
  refine (C.supp.finite_toSet).subset fun w hw => ?_
  by_contra h
  apply hw
  rw [Finset.mem_coe] at h
  simp [flD, sgD, h]

end Lemmas

section Lemmas2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

variable {V W κ ι : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]

end Lemmas2

section Main

example : LineHypothesesOfColumnExtension = ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) [Fintype I]
    {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    (C : ColObj K I) (L : ColLink C Dc) (S : IndefCols Df Dc Sp N) (X : RowExt C S.D) (hu : I → ℝ) (sg : ℝ),
    Df.WF → L.Tied → (∀ u, Nonempty (RowIn S (L.wU u) (L.NuD u) (sgD C u) (hu u))) → ExtHyp C L S X sg →
    RowHyp C (rowArg C L S X hu) sg := rfl

example {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {Bs : DefBase K} {Df : DefSide Bs}
    {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs} (C : ColObj K I) (L : ColLink C Dc) (S : IndefCols Df Dc Sp N)
    (X : RowExt C S.D) (hu : I → ℝ) :
    (rowArg C L S X hu).h = (fun u => hu u - meanLog S.κ) ∧ (rowArg C L S X hu).Ball = (fun u => X.Bf u * C.Vr u Bs.v0) ∧
    (rowArg C L S X hu).cc = dualLat S.RR ∧ (rowArg C L S X hu).X' = dualFrame S.XE ∧ (rowArg C L S X hu).v = Bs.v0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Main

end Formalism.L2.GlobalTheoryTheory.FamRows

import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionSheafQuotient
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace Formalism.MainNotions.Gaps.HeightData

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def toHtData (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) : HtData where
  K := B.KO
  D := WeightFamilies.dimY D j
  δ := G.del
  i := G.iet
  g0 := (g0 D : ℝ)
  L := wL.size
  G := Gc
  PH := PH
  Prw := Prw
  Pet := Pet
  S k := WeightFamilies.meanLogSup B (G.th' k)
  etaPart := j < D.R.m
  Op la := Op X la G.N
  SectionSheafQuotient la := SectionSheafQuotient X la G.w wF
  A0 la := (Qf la).A0
  t la := tL G la
  Pts la := PtsG G la
  ep la ζ := ep (unifO X la G.N) ζ
  f _ ζ := fdeg ζ
  vEt la ζ := (X.vAt la ((Qf la).y ζ) (X.inc _ G.et)).toReal

theorem heights_of_htConcl (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ)
    (h : HtConcl (toHtData G Qf Gc PH Prw Pet)) : Heights Qf Gc PH Prw Pet := by
  exact h

end Formalism.MainNotions.Gaps.HeightData

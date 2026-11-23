import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocal
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocalCOfLen

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

def LenBaseAll (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j), LenBase (X := X) (ka := ka) (wL := wL) (wF := wF)

def LenPoleLAll (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j), LenPoleL (X := X) (ka := ka) (wL := wL) (wF := wF)

theorem theorem_zero_split_of_lengths (hLB : LenBaseAll D B P) (hLP : LenPoleLAll D B P) :
    Conclusion1OfComb (D := D) (B := B) (P := P) := theorem_zero_split_of_local (localC_of_len hLB hLP)

theorem theorem_zero_bundled_of_lengths (hLf : LiftAll D B P) (hLB : LenBaseAll D B P) (hLP : LenPoleLAll D B P) :
    Conclusion1Of2 (D := D) (B := B) (P := P) := theorem_zero_bundled_of_split hLf (theorem_zero_split_of_lengths hLB hLP)

end Formalism.MainNotions.Gaps.EtaleWeightGaps

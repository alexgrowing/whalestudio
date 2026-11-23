import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.HasseKpAlgebraMapKl

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps

def PI.HassePresH : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
    {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j) (β : Idx D j N →₀ ℕ) (x : Lw X la w),
    x ∈ Hfr X la w u → hasse X la w β x ∈ Hfr X la w u

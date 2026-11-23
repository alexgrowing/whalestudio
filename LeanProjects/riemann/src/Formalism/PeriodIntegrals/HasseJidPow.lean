import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.HasseKpAlgebraMapKl

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps

def PI.HasseJidPow : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
    {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j) (β : Idx D j N →₀ ℕ) (a : ℕ)
    (x : Lw X la w),
    x ∈ JHfr X la w u a → hasse X la w β x ∈ JHfr X la w u (a - β.sum fun _ n => n)

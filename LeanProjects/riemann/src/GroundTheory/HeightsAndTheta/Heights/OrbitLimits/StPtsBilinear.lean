import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StokesObjects
import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot PBlk oneLine
  isSmoothHerm_oneLine)

def PtsBilinear.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (T : Type) [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ)
    (v : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ t, IsDegZeroSmooth (u t)) →
    IsDegZeroSmooth v →
    ptsIntegral P (Fin.cons v (pot L)) (fun z => ∑ t, u t z) =
        ∑ t, ptsIntegral P (Fin.cons v (pot L)) (u t) ∧
      ptsIntegral P (Fin.cons (fun z => ∑ t, u t z) (pot L)) v =
        ∑ t, ptsIntegral P (Fin.cons (u t) (pot L)) v

end GroundTheory.Heights₂.Heights

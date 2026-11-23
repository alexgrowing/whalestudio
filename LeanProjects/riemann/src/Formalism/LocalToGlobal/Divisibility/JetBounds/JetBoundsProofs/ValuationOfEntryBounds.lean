import Formalism.LocalToGlobal.Divisibility.JetBounds.PlaceInputAllEntries
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormInvNatCastLeOfDvd

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

theorem valuation_of_entry_bounds {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df1 : DefSide Bs}
    (Dc : DefCols Df1) (u : Dc.Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ) (l : ℕ) [Fact l.Prime] (ι : K →+* ℂ_[l])
    (X : PathData K l Bs.J (Fin (Dc.a u) → K) (Fin (Df1.nV t) → K)) (D : ℕ) (j1 : Bs.J) (s : Bs.J → ℝ)
    (hι : EmbAt w l ι)
    (hX : IsExpansion X ι (Dc.Pt u t) (Nu : Set (Fin (Dc.a u) → K)) (Df1.Mt t : Set (Fin (Df1.nV t) → K)))
    (hc : ColsInt X w (Nu : Set (Fin (Dc.a u) → K))) (hr : RowsInt X w (Df1.Mt t : Set (Fin (Df1.nV t) → K)))
    (hl : LastInt X) (hu : UnitsInt X) (hD : StabDvd X D j1)
    (he : ∀ π j, ‖X.e π j‖ ≤ ‖(l : ℂ_[l])‖ ^ (s j))
    (hs : sgw ≤ (ramw w : ℝ) * ∑ j, (s j - (padicValNat l D : ℝ))) :
    LocalValuationBoundAt Dc u t Nu w sgw := by
  intro φ hφ F hF
  by_cases h0 : Dc.Pt u t φ F = 0
  · exact Or.inl h0
  · right
    have hb := path_height_bound K l Bs.J _ _ X ι D j1 s φ F
      (fun π => embeddingIntegral_holds K w l ι hι _ (hc π φ hφ)) (fun π => embeddingIntegral_holds K w l ι hι _ (hr π F hF)) hl hu hD he
    rw [← hX φ hφ F hF] at hb
    exact hs.trans (embedding_lower_bound K w l ι hι _ _ h0 hb)

end Formalism.L2.DIV

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames ReciprocityTheory.ChartRestriction.G.Pdiv Formalism.L2.Pj
open scoped CategoryTheory.Obj NNReal

def PlaceShiftSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : HeightOneSpectrum (𝓞 E)), ∃ κ₁ κ₂ : ℝ,
      ∀ τ : E →+* ℂ_[ℓ], (∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖τ (a : E)‖ < 1) →
      letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
      ∀ [IsAdicComplete (Ideal.span {(ℓ : 𝓞_ℂ_[ℓ])}) 𝓞_ℂ_[ℓ]]
        (P : Point ℓ (Valued.v : Valuation ℂ_[ℓ] ℝ≥0) 𝓞_ℂ_[ℓ] (𝓞 E)) (p q : ℕ),
        (∀ φ : E →+* ℂ_[ℓ], Module.finrank ℂ_[ℓ] (P.eigW (embO P.integers φ)) =
          open Classical in if φ (H.rt : E) = τ (H.rt : E) then p else q) →
        ∀ (x : Fin p → LieG P.Gt) (x' : Fin q → LieG P.Gt) (g : Matrix (Fin p) (Fin p) ℂ_[ℓ])
          (g' : Matrix (Fin q) (Fin q) ℂ_[ℓ]),
          Submodule.span 𝓞_ℂ_[ℓ] (Set.range fun i => P.bLie (x i)) = P.wRec (embO P.integers τ) →
          Submodule.span 𝓞_ℂ_[ℓ] (Set.range fun i => P.bLie (x' i)) =
            P.wRec ((embO P.integers τ).comp (starRingEnd (𝓞 E))) →
          IsLatBasis ℂ_[ℓ] (open Classical in P.latTQuot (σ := fun φ : E →+* ℂ_[ℓ] => embO P.integers φ)
            (isSplitting_embO P.integers) τ) (fun i => ∑ j, g i j • P.bLie (x j)) →
          IsLatBasis ℂ_[ℓ] (P.latTSub ((embO P.integers τ).comp (starRingEnd (𝓞 E))))
            (fun i => ∑ j, g' i j • P.bLie (x' j)) →
          Real.log ‖g.det‖ - Real.log ‖g'.det‖ = p * κ₁ + q * κ₂

end GlobalTheory.FlatCM

end

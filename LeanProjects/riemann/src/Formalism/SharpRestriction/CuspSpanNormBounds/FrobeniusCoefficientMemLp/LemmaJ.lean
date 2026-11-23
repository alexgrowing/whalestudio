import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open MeasureTheory

noncomputable section

namespace Formalism.MainNotions.S.Pv.LemmaJ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def AmpOrb (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → Cn ≤ Cl →
  ∀ τ w w', HypTT D w w' → ∀ θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
    (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    ∀ (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∃ f : MatKR D.R.k D.R.rS →
        ((toBessel D τ w w' θ W lam' A hW hA hT hT').Wq →L[ℂ] (toBessel D τ w w' θ W lam' A hW hA hT hT').Wp),
      IsKFinCoefH (toBessel D τ w w' θ W lam' A hW hA hT hT').σ f ∧
      ∀ γ : MatKR D.R.k D.R.rS, γ ∈ UH (Hpk D.R.k D.R.rS) → 0 < Gf D.R.k D.R.rS W.z W.z' γ →
        Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS W.z W.z' γ) →
        IsRelStab (toBessel D τ w w' θ W lam' A hW hA hT hT') γ →
        ∀ (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
          IsHaarOn (RStab D.R.k D.R.rS γ) μR →
          IsOrbQuot (toBessel D τ w w' θ W lam' A hW hA hT hT') γ μR ν →
          IsQuotMeas W.μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR →
          A.J νR γ = OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f γ ν

end Formalism.MainNotions.S.Pv.LemmaJ

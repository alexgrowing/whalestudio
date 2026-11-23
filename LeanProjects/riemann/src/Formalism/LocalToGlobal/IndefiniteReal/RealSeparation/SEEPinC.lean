import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SEEPin

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.IndefR.AutomorphicEvaluation
  Formalism.IndefR.Links

namespace Formalism.IndefR.Mi

variable {D : D7} {S : D.what₂.Tau → SPar}

def SEEPinC {M : DSModel (D.sp.Y 0) S} (HE : HMod (MMap M)) (t : Bool) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0))) (E : Submodule ℂ (MMap M)) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (tS : GA D (D.sp.Y 0)) (c κ : ℝ)
    (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (KS : Set X.B.I.GA) (χS : X.B.I.GA → ℂ)
    (sEE : Tw t HE.H →ₗ⋆[ℂ] Tw t (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X)) : Prop :=
  ConjLevel tS⁻¹ J χ (ι ⁻¹' KS) (fun k => χS (ι k)) ∧ 0 < κ ∧
    ∀ (x : Tw t HE.H) (hx : HE.e (Tw.out x) ∈ E),
      sEE x = Tw.mk t ((κ : ℂ) • sEEofTT M μ 𝓕 E X G ι tS c ⟨HE.e (Tw.out x), hx⟩)

end Formalism.IndefR.Mi

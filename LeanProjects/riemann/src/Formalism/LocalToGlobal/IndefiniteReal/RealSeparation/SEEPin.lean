import Formalism.LocalToGlobal.IndefiniteReal.SEEofApply
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.IndefR.AutomorphicEvaluation
  Formalism.IndefR.Links

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

theorem star_cj (t : Bool) (z : ℂ) : star (cj t z) = cj t (star z) := by
  cases t <;> simp [cj]

set_option maxHeartbeats 1000000 in

def sEEcF {M : DSModel (D.sp.Y 0) S} (HE : HMod (MMap M)) {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}
    (f : E →ₗ⋆[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hE : ∀ x, HE.e x ∈ E) (t : Bool) (κ : ℝ) :
    Tw t HE.H →ₗ⋆[ℂ] Tw t (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) where
  toFun x := Tw.mk t ((κ : ℂ) • f ⟨HE.e (Tw.out x), hE _⟩)
  map_add' x y := by
    have e1 : (⟨HE.e (Tw.out (x + y)), hE _⟩ : E) = ⟨HE.e (Tw.out x), hE _⟩ + ⟨HE.e (Tw.out y), hE _⟩ := by
      apply Subtype.ext
      show HE.e (Tw.out x + Tw.out y) = HE.e (Tw.out x) + HE.e (Tw.out y)
      exact map_add _ _ _
    rw [e1, map_add, smul_add]
    rfl
  map_smul' z x := by
    have e1 : (⟨HE.e (Tw.out (z • x)), hE _⟩ : E) = cj t z • ⟨HE.e (Tw.out x), hE _⟩ := by
      apply Subtype.ext
      show HE.e (cj t z • Tw.out x) = cj t z • HE.e (Tw.out x)
      exact map_smul _ _ _
    rw [e1, LinearMap.map_smulₛₗ]
    change Tw.mk t ((κ : ℂ) • ((starRingEnd ℂ) (cj t z) • f ⟨HE.e (Tw.out x), hE _⟩)) =
      Tw.mk t (cj t ((starRingEnd ℂ) z) • ((κ : ℂ) • f ⟨HE.e (Tw.out x), hE _⟩))
    rw [starRingEnd_apply, starRingEnd_apply, star_cj, smul_comm]

def sEEc {M : DSModel (D.sp.Y 0) S} (HE : HMod (MMap M)) {μ : Measure (GA D (D.sp.Y 0))}
    {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
    {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} (h : EvalTie M μ 𝓕 E X G ι c) (hE : ∀ x, HE.e x ∈ E) (t : Bool)
    (κ : ℝ) : Tw t HE.H →ₗ⋆[ℂ] Tw t (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) :=
  sEEcF HE (sEEof h) hE t κ

def SEEPinL {M : DSModel (D.sp.Y 0) S} (HE : HMod (MMap M)) (t : Bool) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (E : Submodule ℂ (MMap M))
    (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (KS : Set X.B.I.GA) (χS : X.B.I.GA → ℂ)
    (sEE : Tw t HE.H →ₗ⋆[ℂ] Tw t (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X)) : Prop :=
  ∃ (tS : GA D (D.sp.Y 0)) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (c : ℝ) (_ : EvalTieT M μ 𝓕 E X G ι tS c) (κ : ℝ),
    ConjLevel tS⁻¹ J χ (ι ⁻¹' KS) (fun k => χS (ι k)) ∧ 0 < κ ∧
      ∀ (x : Tw t HE.H) (hx : HE.e (Tw.out x) ∈ E),
        sEE x = Tw.mk t ((κ : ℂ) • sEEofTT M μ 𝓕 E X G ι tS c ⟨HE.e (Tw.out x), hx⟩)

end Formalism.IndefR.Mi

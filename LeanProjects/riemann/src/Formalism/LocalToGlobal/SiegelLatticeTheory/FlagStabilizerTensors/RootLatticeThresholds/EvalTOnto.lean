import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict
open Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open scoped InnerProductSpace

namespace Formalism.L2.SG.EvalTOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem rows_eq_hom
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)))
    (z : L2X X) (hz : z ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) :
    ∃ Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re, Φ (X.B.tens X.B.w) = z := by
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re
    X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hL X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens
    X.B.tens_spec
  have hz' : z ∈ LinearMap.range (Formalism.L2.SG.RowsDef.evAt X.B.I X.B.μf X.B.fund X.B.σs X.B.R X.B.Re
      (X.B.tens X.B.w)) := by
    rw [hB.2]; exact hz
  obtain ⟨S, hS⟩ := hz'
  exact ⟨S, S.2, hS⟩

variable {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (G : GoodOp X)
  (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec)

def OntoFromHom : Prop :=
  ∀ Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re, ∀ F : EEC X G, Φ (X.B.tens X.B.w) = star (F : L2X X) →
    ∃ T ∈ E, (F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x * t)

variable {X M E G ι t v₀}

end Formalism.L2.SG.EvalTOnto

end

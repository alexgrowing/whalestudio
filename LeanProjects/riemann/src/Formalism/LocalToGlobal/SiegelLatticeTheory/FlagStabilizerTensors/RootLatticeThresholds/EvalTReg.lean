import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.L2.SG.EvalTReg

section Abs

open Formalism.MainNotions.LeviCoordinates

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

theorem reg_toLp (h : rr_FD μ Γ D) {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
    (hR : rr_IsReg μ Γ D R) (f0 : G → ℂ) (hinv : ∀ γ ∈ Γ, ∀ y, f0 (γ * y) = f0 y)
    (hm : MemLp f0 2 (μ.restrict D)) (g : G) :
    ((R g (hm.toLp f0) : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D] fun x => f0 (x * g) := by
  have hmap := rr_map h g
  have h3 : ∀ᵐ x ∂(μ.restrict D), (hm.toLp f0 : G → ℂ) (rr_rep (Γ : Set G) D (x * g)) =
      f0 (rr_rep (Γ : Set G) D (x * g)) := by
    refine ae_of_ae_map (p := fun y => (hm.toLp f0 : G → ℂ) y = f0 y) hmap.1 ?_
    rw [hmap.2]
    exact hm.coeFn_toLp
  filter_upwards [hR g (hm.toLp f0), h3] with x a1 a2
  rw [a1, a2]
  obtain ⟨γ, hγ, e1, -⟩ := rr_rep_spec h (x * g)
  rw [e1, hinv γ hγ]

end Abs

section X

open Formalism.BasicNotions Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.RowDict Formalism.L2.SG.Pf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem reg_toLp_X (f0 : X.B.I.GA → ℂ) (hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, f0 (γ * y) = f0 y)
    (hm : MemLp f0 2 (muX X)) (y : X.B.I.GA) :
    ((X.B.R y (hm.toLp f0) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => f0 (x * y) := by
  have := X.B.sf
  have := X.B.haar
  have := gf_secondCountable X.B.I
  have := muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  exact reg_toLp (rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec)
    (rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec) f0 hinv hm y

end X

section Polar

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

end Polar

section Transfer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}
  {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ}

end Transfer

end Formalism.L2.SG.EvalTReg

end

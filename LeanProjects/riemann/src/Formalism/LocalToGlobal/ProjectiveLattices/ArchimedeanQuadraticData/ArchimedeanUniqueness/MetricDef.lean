import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

noncomputable section

namespace Formalism.L2.Pj.QAt.Arch

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def archA {K₁ : Type} [Field K₁] [NumberField K₁] (n : ℕ) (nth : InfinitePlace K₁ → ℝ)
    (lη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → InfinitePlace K₁ → ℝ) (μ : ArcLt Dw →₀ ℕ)
    (σ : InfinitePlace K₁) : ℝ :=
  -((n : ℝ) / 2) * Real.log (nth σ) - ∑ x ∈ μ.support, (μ x : ℝ) * lη x.1 x.2.2 σ

def IsThNormAt {K₁ : Type} [Field K₁] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁))
    (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec) (σ : K₁ →+* ℂ) (v : ℝ) : Prop :=
  ∃ (P' : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (rig' : LB.Gen (P'.L.pull (eSec P'.A))) (th' : P'.L.Sec)
    (φ : P'.A.left ⟶ P.A.left) (he : eSec P'.A ≫ φ = spMap σ ≫ eSec P.A) (w : LB.Iso P'.L (P.L.pull φ)),
    IsGrpPullback P'.A P.A (spMap σ) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1)) rig'
      (rigPullOf φ (spMap σ) he P.L rig) ∧
    (∀ (j : (P.L.pull φ).ι) (i : P'.L.ι)
      (h : (P.L.pull φ).U j ⊓ P'.L.U i ≤ φ ⁻¹ᵁ P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (th.f (j PUnit.unit)) =
        (show Γ(P'.A.left, (P.L.pull φ).U j ⊓ P'.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (th'.f i)) ∧
    ∃ (u : HolUnif P'.A P'.L P'.g) (Hm : Matrix (Fin P'.g) (Fin P'.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin P'.g → ℂ) → ℂ) (Fd : Set (Fin P'.g → ℂ)),
      u.IsAH Hm χ ∧ u.IsRig rig' ∧ u.IsFn th' θ ∧ IsAddFundamentalDomain u.Λ Fd volume ∧
      v = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal

def IsLieNormAt {K₁ : Type} [Field K₁] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (η : epsR K₁ ⟶ P.A)
    (σ : K₁ →+* ℂ) (v : ℝ) : Prop :=
  ∃ (P' : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull φ))
    (η' : epsR ℂ ⟶ P'.A),
    IsGrpPullback P'.A P.A (spMap σ) φ ∧ w.IsGen ∧ η'.left ≫ φ = spMap (dualMap σ) ≫ η.left ∧
    ∃ (u : HolUnif P'.A P'.L P'.g) (Hm : Matrix (Fin P'.g) (Fin P'.g) ℂ) (χ : u.Λ → ℂ) (z : Fin P'.g → ℂ),
      u.IsAH Hm χ ∧ u.IsDiff z η' ∧ v = Real.log (Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re) / 2

end Formalism.L2.Pj.QAt.Arch

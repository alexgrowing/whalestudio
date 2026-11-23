import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest

noncomputable section
namespace GlobalTheory.FlatPair
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def resRd {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hT : AllTest Xo c) (k : U.Comp) :
    Rul Xo c →+* (↥(U.X k).dom → ℂ) where
  toFun f := fun y => rdU U f k y.1
  map_one' := by
    funext y
    haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, y.2, dif_pos, Pi.one_apply]
    exact congrArg toC (evalAt_one _ _ (U.un k ⟨y.1, y.2⟩) (hT _ _))
  map_mul' f g := by
    funext y
    exact congrFun (congrFun (AllWt.rdU_mul U f g) k) y.1
  map_zero' := by
    funext y
    simp
  map_add' f g := by
    funext y
    simp

theorem resRd_apply {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hT : AllTest Xo c) (k : U.Comp) (f : Rul Xo c)
    (y : ↥(U.X k).dom) : resRd U hT k f y = rdU U f k y.1 := rfl

theorem resRd_smul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hT : AllTest Xo c) (k : U.Comp) (a : c.F) (f : Rul Xo c) :
    resRd U hT k (a • f) = σ a • resRd U hT k f := by
  funext y
  simp [resRd_apply, map_smulₛₗ]

def holAlg (X : Data E r) : Subalgebra ℂ (↥X.dom → ℂ) where
  carrier := {g | ∃ F : Frame X.Ψ r → ℂ, DifferentiableOn ℂ F X.dom ∧ ∀ y, g y = F y.1}
  mul_mem' := by
    rintro g g' ⟨F, hF, hg⟩ ⟨F', hF', hg'⟩
    exact ⟨F * F', hF.mul hF', fun y => by simp [hg, hg']⟩
  add_mem' := by
    rintro g g' ⟨F, hF, hg⟩ ⟨F', hF', hg'⟩
    exact ⟨F + F', hF.add hF', fun y => by simp [hg, hg']⟩
  algebraMap_mem' a := ⟨fun _ => a, differentiableOn_const a, fun y => rfl⟩

end GlobalTheory.FlatPair

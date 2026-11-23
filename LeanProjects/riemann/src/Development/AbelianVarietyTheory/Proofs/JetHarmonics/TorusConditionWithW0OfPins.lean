import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaAdditiveRelations

noncomputable section

namespace GlobalTheory.TorusTieCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
  Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdditiveRelations
open ReciprocityTheory.ChartRestriction.G.I2 (TorusAt Vsp)

section Conj

variable {g : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def toConjLinear (L : (Fin g → ℂ) →ₗ[ℂ] V) : (Fin g → ℂ) →ₛₗ[starRingEnd ℂ] V where
  toFun z := L (star z)
  map_add' z w := by rw [star_add, map_add]
  map_smul' t z := by rw [star_smul, map_smul]; rfl

def ofConjLinear (β : (Fin g → ℂ) →ₛₗ[starRingEnd ℂ] V) : (Fin g → ℂ) →ₗ[ℂ] V where
  toFun z := β (star z)
  map_add' z w := by rw [star_add, map_add]
  map_smul' t z := by rw [star_smul, map_smulₛₗ]; simp

@[simp] theorem toConjLinear_apply (L : (Fin g → ℂ) →ₗ[ℂ] V) (z : Fin g → ℂ) :
    toConjLinear L z = L (star z) := rfl

@[simp] theorem ofConjLinear_apply (β : (Fin g → ℂ) →ₛₗ[starRingEnd ℂ] V) (z : Fin g → ℂ) :
    ofConjLinear β z = β (star z) := rfl

def conjLinearEquiv : ((Fin g → ℂ) →ₗ[ℂ] V) ≃ ((Fin g → ℂ) →ₛₗ[starRingEnd ℂ] V) where
  toFun := toConjLinear
  invFun := ofConjLinear
  left_inv L := LinearMap.ext fun z => by simp
  right_inv β := LinearMap.ext fun z => by simp

end Conj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (Wu : UnitAt W) (A : TorusAt (U.X k) x.1) (L : (Fin W.g → ℂ) →ₗ[ℂ] Vsp A.T.dim)

variable {W Wu A L}

variable (W Wu A L)

variable {W Wu A L}

def withW0 {X : Data E r} {y : Frame X.Ψ r} (A : TorusAt X y) (w : 𝓞 E)
    (hw : ∀ v ∈ X.Λ, (A.T.eps (A.φ v) : ℝ) =
      Real.cos (Real.pi * (ReciprocityTheory.ChartRestriction.G.I2.Hf (A.φ v) (A.φ ((w : E) • v))).im)) : TorusAt X y :=
  { A with w0 := w, eps_eq := hw }

variable (W Wu)

end GlobalTheory.TorusTieCompare

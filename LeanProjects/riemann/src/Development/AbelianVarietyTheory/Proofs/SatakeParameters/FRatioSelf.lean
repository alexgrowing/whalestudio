import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

variable {R : Type} [CommRing R] {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace R N)

def fOpen (g : MvPolynomial (Fin (N + 1)) R) : X.Opens := ι ⁻¹ᵁ Proj.basicOpen (grading R N) g

def fRatio {n : ℕ} (f g : MvPolynomial (Fin (N + 1)) R) (hf : f ∈ grading R N n) (hg : g ∈ grading R N n) :
    Γ(X, fOpen ι g) :=
  (ι.app (Proj.basicOpen (grading R N) g)).hom (GlobalTheory.ProjFrac.frac (grading R N) _ f g hf hg le_rfl)

theorem fRatio_self {n : ℕ} (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ grading R N n) :
    fRatio ι g g hg hg = 1 := by
  unfold fRatio
  rw [GlobalTheory.ProjFrac.frac_self]
  exact map_one _

theorem mem_fOpen (g : MvPolynomial (Fin (N + 1)) R) (z : X) :
    z ∈ fOpen ι g ↔ g ∉ (ι.base z).asHomogeneousIdeal := Iff.rfl

end GlobalTheory.EtProj

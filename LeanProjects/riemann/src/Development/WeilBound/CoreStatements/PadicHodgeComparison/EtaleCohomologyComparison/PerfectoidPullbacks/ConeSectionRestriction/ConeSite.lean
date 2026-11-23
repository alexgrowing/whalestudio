import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

def wch (i : X ⟶ PSpace K N) (j : Fin (N + 1)) : X.Opens := i ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)

def uy (i : X ⟶ PSpace K N) {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (k : Fin m) : X.Opens :=
  i ⁻¹ᵁ Proj.basicOpen _ (y k)

def wK (q : X ⟶ Spec (CommRingCat.of K)) (i : X ⟶ PSpace K N) {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (s : ℕ) (k : Fin m) : ObjectProperty (Thick (smFun X q)) :=
  St (TF 1 s) (Set.range fun j => uy i y k ⊓ wch i j)

def wU (q : X ⟶ Spec (CommRingCat.of K)) (i : X ⟶ PSpace K N) {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (s : ℕ) : ObjectProperty (Thick (smFun X q)) :=
  fun T => ∃ k, wK q i y s k T

def yQ {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m) :
    Γ(PSpace K N, Proj.basicOpen _ (y k')) :=
  (Proj.awayToSection _ (y k')).hom
    (HomogeneousLocalization.Away.mk _ ((MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')) 1 (y k)
      (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)))

end CrystallineSemistableComparison.Pb

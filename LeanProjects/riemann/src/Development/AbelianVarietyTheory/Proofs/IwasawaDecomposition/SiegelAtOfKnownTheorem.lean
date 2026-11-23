import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLoc

def SiegAt (g : ℕ) (φ : InvFun ℤ) (n : ℕ) : Prop :=
  ∃ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (_ : IsOpenImmersion j)
    (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ),
    IsProjOver s ∧ SmoothOfRelativeDimension (g * (g + 1) / 2) s ∧ j ≫ s = F.s ∧
    (∀ x : S, x ∈ closure (Set.range j ∩ s ⁻¹' {s x})) ∧
    IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j ∧
    1 ≤ d ∧ (∀ x : S, HasChart F s j e φ BD d x) ∧
    1 ≤ N ∧ IsGenerated (lbPow (hodge G g) N) ∧
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (hodge G g) (N * k)) (CechPic.dual BD.lb))

theorem siegAt_of_siegelToroidalIntegral (h : GlobalTheory.Published.SiegelToroidalIntegral) (g : ℕ) (hg : 1 ≤ g) :
    ∃ φ : InvFun ℤ, IsPolFan id g φ ∧ ∀ n : ℕ, 3 ≤ n → Odd n → SiegAt g φ n :=
  h g hg

def AgreesPsd (g : ℕ) (φs φ : InvFun ℤ) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Projective ℤ X], Module.finrank ℤ X ≤ g →
    ∀ B ∈ psdCone (id : ℤ → ℤ) X, evalR φs B = evalR φ B

end GlobalTheory.SiegLoc

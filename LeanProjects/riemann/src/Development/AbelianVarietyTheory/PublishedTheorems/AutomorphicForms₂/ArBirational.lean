import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.Published

def ArBirational : Prop :=
  ∀ (k : Type) [CommRing k] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (p : X ⟶ Sp k) (p' : X' ⟶ Sp k) (D : ℕ),
    IsArithVar p D → IsArithVar p' D → GenSmooth p D → GenSmooth p' D →
      ∀ (π : X' ⟶ X) (hπ : π ≫ p = p') (U : X.Opens), (U : Set X).Nonempty →
        IsIso (π ∣_ U) → ∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a → (L.pull π hπ).IsSelfInter a

def ChernDegree : Prop :=
  ∀ (F : Type) [Field F] (Y : Var F) (σ : F →+* ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), Presents Δ L r →
    ∀ φ : Weight Y.str σ L, φ.IsCInf →
      φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧
        φ.chernInt Y.dim Set.univ (fun _ => 1) = (Y.inter (fun _ => Δ) : ℝ)

def ArDegree : Prop := ArBirational ∧ ChernDegree

end GlobalTheory.Published

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.Published

def ChernDegreeComplex : Prop :=
  ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), Presents Δ L r →
    ∀ φ : Weight Y.str (RingHom.id ℂ) L, φ.IsCInf →
      φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧
        φ.chernInt Y.dim Set.univ (fun _ => 1) = (Y.inter (fun _ => Δ) : ℝ)

end GlobalTheory.Published

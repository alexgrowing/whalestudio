import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

noncomputable section

namespace GlobalTheory.OmitFlag

open CategoryTheory.Limits

def IsPairBundle {B G : Scheme.{0}} (γ : G ⟶ B) (E : B.Modules) (m₁ m₂ : ℕ) {S P : G.Modules} (s : S ⟶ P)
    (j : P ⟶ (Scheme.Modules.pullback γ).obj E) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ B) (S' P' : T.Modules) (s' : S' ⟶ P') (j' : P' ⟶ (Scheme.Modules.pullback g).obj E),
    GlobalTheory.VB.IsSubbundle s' → GlobalTheory.VB.IsSubbundle j' → GlobalTheory.VB.IsVB S' m₁ → GlobalTheory.VB.IsVB P' m₂ →
    ∃! g' : T ⟶ G, ∃ w : g' ≫ γ = g, ∃ (eS : (Scheme.Modules.pullback g').obj S ≅ S')
      (eP : (Scheme.Modules.pullback g').obj P ≅ P'),
      eP.hom ≫ j' = (Scheme.Modules.pullback g').map j ≫ (Scheme.Modules.pullbackComp g' γ).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E ∧
      eS.hom ≫ s' = (Scheme.Modules.pullback g').map s ≫ eP.hom

def fam {B G : Scheme.{0}} (γ : G ⟶ B) {ι : Type} (E : ι → B.Modules) (a : ι) {S P : G.Modules} (s : S ⟶ P)
    (j : P ⟶ (Scheme.Modules.pullback γ).obj (E a)) : ({b // b ≠ a} ⊕ Bool) → G.Modules :=
  Sum.elim (fun b => (Scheme.Modules.pullback γ).obj (E b.1)) fun t => cond t S (cokernel j)

def rk {ι : Type} (r : ι → ℕ) (a : ι) (m₁ m₂ : ℕ) : ({b // b ≠ a} ⊕ Bool) → ℕ :=
  Sum.elim (fun b => r b.1) fun t => cond t m₁ (r a - m₂)

end GlobalTheory.OmitFlag

end

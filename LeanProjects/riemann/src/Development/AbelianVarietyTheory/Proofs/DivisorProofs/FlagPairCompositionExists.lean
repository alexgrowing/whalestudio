import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullbackComposition

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.Vert.Model.FlagPair

theorem exists_chain_pull_comp' {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Z Z₁ Z₂ : Model O} {f : Z₁.X ⟶ Z.X} {g : Z₂.X ⟶ Z₁.X}
    (hf : f ≫ Z.str = Z₁.str) (hg : g ≫ Z₁.str = Z₂.str) (hfg : (g ≫ f) ≫ Z.str = Z₂.str)
    {E E' E'' : Z.X.Modules} (φ : Z.GenIso E E') (φ' : Z.GenIso E' E'') (N : ℕ)
    (P : FlagPair ((φ.pull hf).pull hg) N) (Q : FlagPair ((φ'.pull hf).pull hg) N)
    (hQ : Q.fl = P.fl') :
    ∃ (P₁ : FlagPair (φ.pull hfg) N) (Q₁ : FlagPair (φ'.pull hfg) N), Q₁.fl = P₁.fl' :=
  ⟨P.transport ((Scheme.Modules.pullbackComp g f).app E) ((Scheme.Modules.pullbackComp g f).app E')
      (GenIso.pull_pull_hom' hf hg hfg φ),
    Q.transport ((Scheme.Modules.pullbackComp g f).app E') ((Scheme.Modules.pullbackComp g f).app E'')
      (GenIso.pull_pull_hom' hf hg hfg φ'),
    congrArg (fun fl => GlobalTheory.Vert.Flag.ofIso fl ((Scheme.Modules.pullbackComp g f).app E')) hQ⟩

theorem exists_chain_pull_comp : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z Z₁ Z₂ : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom Z₁ Z) (g : GlobalTheory.Vert.Model.Hom Z₂ Z₁) (E E' E'' : Z.X.Modules) (φ : Z.GenIso E E') (φ' : Z.GenIso E' E'') (N : ℕ) (P : GlobalTheory.Vert.Model.FlagPair ((φ.pull f.comp_str).pull g.comp_str) N) (Q : GlobalTheory.Vert.Model.FlagPair ((φ'.pull f.comp_str).pull g.comp_str) N), Q.fl = P.fl' → ∃ (P₁ : GlobalTheory.Vert.Model.FlagPair (φ.pull (g.comp f).comp_str) N) (Q₁ : GlobalTheory.Vert.Model.FlagPair (φ'.pull (g.comp f).comp_str) N), Q₁.fl = P₁.fl' :=
  fun _ _ _ _ _ _ _ f g _ _ _ φ φ' N P Q hQ =>
    exists_chain_pull_comp' f.comp_str g.comp_str (g.comp f).comp_str φ φ' N P Q hQ

end GlobalTheory.Vert.Model.FlagPair

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateTangentCombinationEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_tangent_combination_eq_prod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {m : ℕ} (v' : Fin m → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (cf : Fin m → Γ(X, U.1)) (va : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U →
    ∀ (g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G) (y : Fin m → (overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G)),
    (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) → IsCombAtG t (GlobalTheory.LogKS.chart U) v' cf va →
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ → (∀ c, (y c).left = spMap (dualMap φ) ≫ v' c) →
    (∀ c, smT (g₀ ≫ t.G.hom) 0 (y c) = 1) ∧
      ∀ w, GlobalTheory.LogKS.IsTranslate t φ g₀ va w →
        w = (g' * (List.ofFn fun c => smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c)).prod).left := by
  first | exact @GlobalTheory.LogKSDiv.translate_comb | exact GlobalTheory.LogKSDiv.translate_comb | (intros; apply GlobalTheory.LogKSDiv.translate_comb <;> assumption)

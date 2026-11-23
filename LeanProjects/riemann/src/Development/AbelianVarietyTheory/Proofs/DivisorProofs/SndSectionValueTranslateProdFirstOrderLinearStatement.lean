import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinear
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
theorem _root_.GlobalTheory.T.snd_sectionValue_translate_prod_first_order_linear : ∀ {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G]
    (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G),
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ →
    ∀ {m : ℕ} (y : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (r : Fin m → S), (∀ c, smT x0 0 (y c) = 1) →
    ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O →
    (valR (g' * (List.ofFn fun c => smT x0 (r c) (y c)).prod).left O f).snd =
      ∑ c, r c * (valR (g' * y c).left O f).snd := by
  first | exact @GlobalTheory.KSLin.snd_valR_translate_prod | exact GlobalTheory.KSLin.snd_valR_translate_prod | (intros; apply GlobalTheory.KSLin.snd_valR_translate_prod <;> assumption)

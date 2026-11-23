import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleExtensionTranslateOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundle_extension_translate_open : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L.IsLB → ExtLam G L PP → ∀ (O : G.left.Opens) (N : LB O.toScheme), N.IsLB → LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, ∃ N' : LB ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).toScheme, N'.IsLB ∧ LBIso (N'.pull (pullback.fst ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) := by
  first | exact @GlobalTheory.Mum.exists_ext_translate | exact GlobalTheory.Mum.exists_ext_translate | (intros; apply GlobalTheory.Mum.exists_ext_translate <;> assumption)

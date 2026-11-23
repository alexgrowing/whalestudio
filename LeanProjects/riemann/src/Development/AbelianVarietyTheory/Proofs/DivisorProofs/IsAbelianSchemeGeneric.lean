import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RetractGeneric

theorem isProper_of_retract {S : Scheme.{0}} {X Y : Over S} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) (hY : IsProper Y.hom) : IsProper X.hom := by
  have hl : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, h, Over.id_left]
  have h1 : IsSeparated (r.left ≫ X.hom) := by rw [Over.w r]; infer_instance
  have h2 : IsSeparated r.left := IsSeparated.of_comp r.left X.hom
  have h3 : IsClosedImmersion (i.left ≫ r.left) := by rw [hl]; infer_instance
  have h4 : IsClosedImmersion i.left := IsClosedImmersion.of_comp i.left r.left
  rw [← Over.w i]
  infer_instance

theorem isAbelianScheme_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ((Over.pullback (jK R)).obj G' ≅ A'.A) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme ((Over.pullback (jK R)).obj G) := by
  intro R _ _ A' G' _ _ _ e G _ _ hG inc pr _ _ h
  have hK := IsSemiAbelian.pullback (jK R) G hG
  have hp : IsProper ((Over.pullback (jK R)).obj G).hom :=
    isProper_of_retract ((Over.pullback (jK R)).map inc ≫ e.hom)
      (e.inv ≫ (Over.pullback (jK R)).map pr)
      (by rw [Category.assoc, e.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, h,
        CategoryTheory.Functor.map_id]) A'.isAb.proper
  exact ⟨hK.comm, hK.smooth, hp, hK.geomConnected⟩

end GlobalTheory.Mum.RetractGeneric

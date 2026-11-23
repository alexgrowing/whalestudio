import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.norm_algebraMap_base_le_one_of_placesOver :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : HeightOneSpectrum (𝓞 F)) (w w' : PlacesOver E q) (a : F),
        ‖algebraMap E (w.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 → ‖algebraMap E (w'.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 := by
  intro F E _ _ _ _ _ q w w' a
  have key : ∀ u : PlacesOver E q,
      ‖algebraMap E (u.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 ↔
        Valued.v (algebraMap F (q.adicCompletion F) a) ≤ 1 := by
    intro u
    rw [Valued.toNormedField.norm_le_one_iff,
      ← IsScalarTower.algebraMap_apply F E (u.1.adicCompletion E),
      ← completionMap_algebraMap q u.1, valued_completionMap]
    exact pow_le_one_iff (Ideal.ramificationIdx_pos u.1.asIdeal (𝓞 F)).ne'
  exact fun h => (key w').2 ((key w).1 h)

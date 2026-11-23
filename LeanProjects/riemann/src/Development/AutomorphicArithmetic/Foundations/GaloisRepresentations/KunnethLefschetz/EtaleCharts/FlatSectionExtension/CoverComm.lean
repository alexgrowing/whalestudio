import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.coverComm :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i), rhoP B j r hw ≫ cP B = eP B j ≫ r ∧ tauP B j ≫ D.f = eP B j ≫ j := by
  intro K _ W Z Y q i π D d B T j r hw
  constructor
  · refine Sigma.hom_ext _ _ fun p => ?_
    have h1 : wI B p.1 ≫ cP B = (oW B p.1).ι := by
      simp only [wI, cP, Sigma.ι_desc]
    have h2 : rhoC B j r hw p ≫ (oW B p.1).ι = (oT B j p).ι ≫ r := by
      simp only [rhoC, IsOpenImmersion.lift_fac]
    simp only [rhoP, eP, Sigma.ι_desc_assoc, Category.assoc, h1, h2]
  · refine Sigma.hom_ext _ _ fun p => ?_
    simp only [tauP, eP, Sigma.ι_desc_assoc, secOf_f]

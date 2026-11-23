import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatOne

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatOne :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a : V ⟶ WP B), GMat B a a 1 := by
  intro K _ W Z Y q i π D d B V a x
  obtain ⟨U, α, a₁, hx, ha⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a x
  refine ⟨U, α, α, a₁, a₁, hx, ha, ha, ?_⟩
  have hc : U.ι ≫ a ≫ cP B = a₁ ≫ (oW B α).ι := by
    have h : wI B α ≫ cP B = (oW B α).ι := by
      simp [wI, cP]
    rw [← Category.assoc, show U.ι ≫ a = a₁ ≫ wI B α from ha, Category.assoc, h]
  have h1 : (1 : Matrix (Fin d) (Fin d) Γ(V, ⊤)).map U.ι.appTop.hom = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1]
  refine locMatOne B α _ fun y => ?_
  rw [hc, Category.assoc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (a₁ y).2

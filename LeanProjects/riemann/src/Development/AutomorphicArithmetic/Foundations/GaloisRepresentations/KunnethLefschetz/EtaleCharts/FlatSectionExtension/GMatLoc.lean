import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaDisj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatLocal

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatLoc :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)) (α β : B.ι) (a₁ : V ⟶ (oW B α : Scheme.{0})) (b₁ : V ⟶ (oW B β : Scheme.{0})), a = a₁ ≫ wI B α → b = b₁ ≫ wI B β → GMat B a b M → LocMat B α β (a ≫ cP B) M := by
  intro K _ W Z Y q i π D d B V a b M α β a₁ b₁ ha hb hG
  refine UpperTheory.Gal.KunnethLefschetz.G.PX.locMatLocal B α β (a ≫ cP B) M fun x => ?_
  obtain ⟨U, α', β', a', b', hx, h1, h2, hL⟩ := hG x
  have e1 : α' = α := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun γ : B.ι => (oW B γ : Scheme.{0})) a' (U.ι ≫ a₁) (⟨x, hx⟩ : U) ?_
    have h : a' ≫ wI B α' = (U.ι ≫ a₁) ≫ wI B α := by
      rw [← h1, ha, Category.assoc]
    exact h
  have e2 : β' = β := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun γ : B.ι => (oW B γ : Scheme.{0})) b' (U.ι ≫ b₁) (⟨x, hx⟩ : U) ?_
    have h : b' ≫ wI B β' = (U.ι ≫ b₁) ≫ wI B β := by
      rw [← h2, hb, Category.assoc]
    exact h
  subst e1 e2
  exact ⟨U, hx, hL⟩

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaDisj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatComp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem map_map_appTop {A B C : Scheme.{0}} {d : ℕ} (f : A ⟶ B) (g : B ⟶ C)
    (M : Matrix (Fin d) (Fin d) Γ(C, ⊤)) :
    (M.map g.appTop.hom).map f.appTop.hom = M.map (f ≫ g).appTop.hom := by
  ext m n
  simp only [Matrix.map_apply, Scheme.Hom.comp_appTop]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatComp :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b k : V ⟶ WP B) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), a ≫ cP B = b ≫ cP B → GMat B a b M → GMat B b k M' → GMat B a k (M' * M) := by
  intro K _ W Z Y q i π D d B V a b k M M' hab h₁ h₂ x
  obtain ⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩ := h₁ x
  obtain ⟨U', β', γ, b₂, k₂, hx', hb', hk', hL'⟩ := h₂ x
  let e : ((U ⊓ U' : V.Opens) : Scheme.{0}) ⟶ U := V.homOfLE inf_le_left
  let e' : ((U ⊓ U' : V.Opens) : Scheme.{0}) ⟶ U' := V.homOfLE inf_le_right
  have he : e ≫ U.ι = (U ⊓ U').ι := V.homOfLE_ι _
  have he' : e' ≫ U'.ι = (U ⊓ U').ι := V.homOfLE_ι _
  have hβ : β = β' := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (e ≫ b₁) (e' ≫ b₂)
      (⟨x, hx, hx'⟩ : ((U ⊓ U' : V.Opens) : Scheme.{0})) ?_
    change (e ≫ b₁) ≫ wI B β = (e' ≫ b₂) ≫ wI B β'
    rw [Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, he, he']
  subst hβ
  refine ⟨U ⊓ U', α, γ, e ≫ a₁, e' ≫ k₂, ⟨hx, hx'⟩, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← ha, ← Category.assoc, he]
  · rw [Category.assoc, ← hk', ← Category.assoc, he']
  · have n₁ := UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat B α β e _ _ hL
    have n₂ := UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat B β γ e' _ _ hL'
    rw [map_map_appTop, he, ← Category.assoc, he] at n₁
    rw [map_map_appTop, he', ← Category.assoc, he', ← hab] at n₂
    have := UpperTheory.Gal.KunnethLefschetz.G.PX.locMatComp B α β γ _ _ _ n₁ n₂
    rwa [← Matrix.map_mul] at this

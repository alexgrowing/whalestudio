import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatUnique
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatOne

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.existsG :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d), ∃ g : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B), a ≫ cP B = b ≫ cP B → GL (Fin d) Γ(V, ⊤), (∀ {V' V : Scheme.{0}} (s : V' ⟶ V) (a b : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B), g (s ≫ a) (s ≫ b) (by rw [Category.assoc, h, Category.assoc]) = Matrix.GeneralLinearGroup.map s.appTop.hom (g a b h)) ∧ (∀ {V : Scheme.{0}} (a b k : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B) (h' : b ≫ cP B = k ≫ cP B), g b k h' * g a b h = g a k (h.trans h')) ∧ ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B), GMat B a b (g a b h : Matrix (Fin d) (Fin d) Γ(V, ⊤)) := by
  intro K _ W Z Y q i π D d B
  have hinv : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B),
      (gMatExists B b a h.symm).choose * (gMatExists B a b h).choose = 1 := fun a b h =>
    gMatUnique B a a _ _
      (gMatComp B a b a _ _ h (gMatExists B a b h).choose_spec (gMatExists B b a h.symm).choose_spec)
      (gMatOne B a)
  refine ⟨fun {V} a b h => ⟨(gMatExists B a b h).choose, (gMatExists B b a h.symm).choose,
    hinv b a h.symm, hinv a b h⟩, ?_, ?_, ?_⟩
  · intro V' V s a b h
    apply Units.ext
    exact gMatUnique B (s ≫ a) (s ≫ b) _ _ (gMatExists B (s ≫ a) (s ≫ b) (by rw [Category.assoc, h, Category.assoc])).choose_spec
      (gMatNat B s a b _ (gMatExists B a b h).choose_spec)
  · intro V a b k h h'
    apply Units.ext
    exact gMatUnique B a k _ _
      (gMatComp B a b k _ _ h (gMatExists B a b h).choose_spec (gMatExists B b k h').choose_spec)
      (gMatExists B a k (h.trans h')).choose_spec
  · intro V a b h
    exact (gMatExists B a b h).choose_spec

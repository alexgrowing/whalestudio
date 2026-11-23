import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

theorem UpperTheory.existsUnique_simplex_pullback_of_map_eq :
    ∀ {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) (n : ℕ) (U : Scheme.{0}) (s : Sx X n U) (t : Sx Y n U),
        Sx.map f s = Sx.map g t →
        ∃! z : Sx (pullback f g) n U, Sx.map (pullback.fst f g) z = s ∧ Sx.map (pullback.snd f g) z = t := by
  intro X Y Z f g n U s t h
  let G : Spc ⥤ Type := (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk n)) ⋙
    (evaluation Scheme.{0}ᵒᵖ Type).obj (op U)
  have sq : IsPullback (G.map (pullback.fst f g)) (G.map (pullback.snd f g)) (G.map f) (G.map g) :=
    (IsPullback.of_hasPullback f g).map G
  obtain ⟨z, h1, h2⟩ := Types.exists_of_isPullback sq s t h
  refine ⟨z, ⟨h1, h2⟩, ?_⟩
  rintro z' ⟨h1', h2'⟩
  exact Types.ext_of_isPullback sq (h1'.trans h1.symm) (h2'.trans h2.symm)

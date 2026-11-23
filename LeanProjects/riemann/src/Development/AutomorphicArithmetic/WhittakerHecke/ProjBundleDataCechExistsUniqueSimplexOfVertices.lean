import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem comp_hom_eq_of_coords {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (U : Scheme.{0})
    (a b : Sx (cech P.e) 0 U)
    (hab : ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) a = ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) b) :
    pts P.e a 0 ≫ P.e = pts P.e b 0 ≫ P.e := by
  have hq : (⟦P.sv (Sx.map P.bunF a) 0⟧ : Quotient (P.relS U)) = ⟦P.sv (Sx.map P.bunF b) 0⟧ := hab
  have hr := Quotient.exact hq
  change P.rel U _ _ at hr
  rw [PBData.sv_bunF, PBData.sv_bunF] at hr
  obtain ⟨h, u, hu⟩ := hr
  exact P.inj _ _ h u hu

theorem UpperTheory.projBundleData_cech_existsUnique_simplex_of_vertices :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → Sx (cech P.e) 0 U),
        (∀ i j, ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) (t i) = ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) (t j)) →
        ∃! z : Sx (cech P.e) n U, ∀ i, Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i := by
  intro T W r d P n U t ht
  let y : Fin (n + 1) → (U ⟶ P.T') := fun i => pts P.e (t i) 0
  have hy : ∀ i, y i ≫ P.e = y 0 ≫ P.e := fun i => comp_hom_eq_of_coords P U (t i) (t 0) (ht i 0)
  have key : ∀ (z : Sx (cech P.e) n U) (i : Fin (n + 1)),
      Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i ↔ pts P.e z i = y i := by
    intro z i
    constructor
    · intro h
      have := congrFun (congrArg (pts P.e) h) 0
      rw [pts_along] at this
      simpa using this
    · intro h
      apply pts_inj
      funext j
      rw [pts_along]
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hj
      simpa using h
  refine ⟨cechPt P.e n (y 0 ≫ P.e) y hy, fun i => (key _ i).2 (by rw [pts_cechPt]), ?_⟩
  intro z hz
  apply pts_inj
  rw [pts_cechPt]
  funext i
  exact (key z i).1 (hz i)

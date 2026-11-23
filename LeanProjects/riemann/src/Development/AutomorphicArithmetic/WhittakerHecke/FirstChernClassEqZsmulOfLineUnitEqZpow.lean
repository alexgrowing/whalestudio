import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private noncomputable def trivNat : glCat 1 ⟶ glCat 1 where
  app A := (SingleObj.mapHom _ _ (1 : GL (Fin 1) A →* GL (Fin 1) A)).toCatHom
  naturality A B f := by
    have : (1 : GL (Fin 1) B →* GL (Fin 1) B).comp (Matrix.GeneralLinearGroup.map f.hom) =
        (Matrix.GeneralLinearGroup.map f.hom).comp (1 : GL (Fin 1) A →* GL (Fin 1) A) := by
      ext x : 1
      simp
    change (SingleObj.mapHom _ _ ((1 : GL (Fin 1) B →* GL (Fin 1) B).comp (Matrix.GeneralLinearGroup.map f.hom))).toCatHom =
      (SingleObj.mapHom _ _ ((Matrix.GeneralLinearGroup.map f.hom).comp (1 : GL (Fin 1) A →* GL (Fin 1) A))).toCatHom
    rw [this]

private theorem lineUnit_triv {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (y : Sx E 1 U) :
    lineUnit (L ≫ ofCatMap trivNat) y = 1 := by
  unfold lineUnit
  simp only [ofCatMap]
  have h : glMat ((ConcreteCategory.hom ((nerveMap (trivNat.app Γ(U, ⊤)).toFunctor).app (op ⦋1⦌)))
      ((ConcreteCategory.hom ((L.app (op ⦋1⦌)).app (op U))) y)) = 1 := rfl
  exact (congrArg Matrix.GeneralLinearGroup.det h).trans (map_one _)

theorem UpperTheory.firstChernClass_eq_zsmul_of_lineUnit_eq_zpow :
    DivisorAdditivity → ∀ (q : ℕ) [NeZero q] {E : Spc} (L M : E ⟶ ofCat (glCat 1)) (ε : ℤˣ), Inv q E →
        (∀ (U : Scheme.{0}) (y : Sx E 1 U), lineUnit L y = lineUnit M y ^ (ε : ℤ)) → c1 q L = (ε : ℤ) • c1 q M := by
  intro hA q _ E L M ε hE hLM
  have add : ∀ (L M N : E ⟶ ofCat (glCat 1)), GlobalTheory.EtC.Inv q E →
      (∀ (U : Scheme) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) →
        c1 q N = c1 q L + c1 q M := fun L M N => (hA q).1 L M N
  set T := L ≫ ofCatMap trivNat with hT
  have hT1 : ∀ (U : Scheme.{0}) (y : Sx E 1 U), lineUnit T y = 1 := fun U y => lineUnit_triv L y
  have h0 := add T T T hE (fun U x => by rw [hT1 U x]; simp)
  have hc : c1 q T = 0 := left_eq_add.mp h0
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have h1 := add M T L hE (fun U x => by rw [hLM U x, hT1 U x]; simp)
    rw [h1, hc, add_zero]
    simp
  · have h1 := add L M T hE (fun U x => by rw [hT1 U x, hLM U x]; simp)
    rw [hc] at h1
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul]
    exact eq_neg_of_add_eq_zero_left h1.symm

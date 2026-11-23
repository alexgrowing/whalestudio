import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem isPullback_lift_fst {X Y S T : Scheme.{0}} (p : X ⟶ S) (q : Y ⟶ S) (t : T ⟶ S) (u : X ⟶ Y)
    (hu : u ≫ q = p) (w : (pullback.fst p t ≫ u) ≫ q = pullback.snd p t ≫ t) :
    IsPullback (pullback.lift (pullback.fst p t ≫ u) (pullback.snd p t) w) (pullback.fst p t)
      (pullback.fst q t) u := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback q t).flip
  rw [pullback.lift_snd, hu]
  exact (IsPullback.of_hasPullback p t).flip

theorem UpperTheory.Gal.KunnethLefschetz.geomPb_holds :
    UpperTheory.Gal.KunnethLefschetz.GeomPb := by
  unfold UpperTheory.Gal.KunnethLefschetz.GeomPb
  intro l _ K M N u hu
  exact IsPullback.paste_vert
    (isPullback_lift_fst M.q N.q _ (Model.genMap u hu) (Model.genMap_q u hu) _)
    (isPullback_lift_fst M.p N.p _ u hu _)

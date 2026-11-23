import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.relIndex_stabilizer_order_level_zero :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → (Hu O (yy π 0 x)).relIndex (Gu O τ) = 1 := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc
  have hy : yy π 0 x = x := by simp [yy]
  have hO : Ord O (yy π 0 x) = Mx O τ := by
    rw [hy, Gen1.span L hc.gen]
    rfl
  rw [Subgroup.relIndex_eq_one]
  intro u hu
  show PS.ml u (Ord O (yy π 0 x)) = Ord O (yy π 0 x)
  rw [hO]
  exact ml_Mx hu.1 hu.2

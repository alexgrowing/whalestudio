import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.IndPerm

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.shapiro :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (x : X) (n : ℕ),
      Nonempty (groupHomology (permRep G X) n ≃+ HZ (MulAction.stabilizer G x) n) := by
  intro G X _ _ _ x n
  classical
  obtain ⟨e⟩ := indPerm G X x
  let i1 := (groupHomology.functor ℤ G n).mapIso e.symm
  let i2 := groupHomology.indIso (MulAction.stabilizer G x) (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) n
  exact ⟨(i1 ≪≫ i2).toLinearEquiv.toAddEquiv⟩

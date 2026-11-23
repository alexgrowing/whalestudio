import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.count :
    UpperTheory.V.Lit.Bor.Count := by
  classical
  intro X S deg κ hκ
  have hq : ∀ q, Cardinal.mk {x : S // deg x = q} ≤ κ q := by
    intro q
    let e := Fintype.equivFin {x : S // deg x = q}
    rw [Cardinal.mk_fintype]
    refine hκ q _ (fun i => ((e.symm i).1 : X)) ?_ (fun i => ⟨(e.symm i).1.2, (e.symm i).2⟩)
    intro i j hij
    exact e.symm.injective (Subtype.ext (Subtype.ext hij))
  calc (S.card : Cardinal) = Cardinal.mk S := (Cardinal.mk_coe_finset).symm
    _ = Cardinal.mk (Σ q, {x : S // deg x = q}) :=
        (Cardinal.mk_congr (Equiv.sigmaFiberEquiv (fun x : S => deg x))).symm
    _ = Cardinal.sum (fun q => Cardinal.mk {x : S // deg x = q}) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum κ := Cardinal.sum_le_sum _ _ hq

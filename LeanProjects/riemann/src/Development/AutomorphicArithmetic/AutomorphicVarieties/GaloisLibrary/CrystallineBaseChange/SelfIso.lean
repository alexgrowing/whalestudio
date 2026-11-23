import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.V.Br.selfIso :
    UpperTheory.V.Br.SelfIso := by
  intro H F _ _ _ a ha π η h2 h
  have hd : ∀ z, TR.dchi η z = 0 := fun z => by
    have e := TR.dchi_mul η η z
    rw [← pow_two, h2, TR.dchi_one] at e
    linear_combination (-1 / 2 : ℂ) * e
  obtain ⟨S, hS⟩ : π.Iso (π.twist η) := H F a ha _ _ (by
    filter_upwards [h] with w ⟨hu, B, hB, hE⟩
    exact ⟨B, hB, hE ▸ hB.twist hu⟩)
  have key : ∀ o φ, (S.trans (π.toTwist η).symm) (π.op o φ) =
      ((TR.opMul η o : ℂˣ) : ℂ) • π.op o ((S.trans (π.toTwist η).symm) φ) +
        TR.opAdd η o • (S.trans (π.toTwist η).symm) φ := fun o φ => by
    apply (π.toTwist η).injective
    rw [← TR.CuspSub.op_toTwist]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hS]
  refine ⟨S.trans (π.toTwist η).symm, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  all_goals rw [key]; simp [TR.opMul, TR.opAdd, hd]

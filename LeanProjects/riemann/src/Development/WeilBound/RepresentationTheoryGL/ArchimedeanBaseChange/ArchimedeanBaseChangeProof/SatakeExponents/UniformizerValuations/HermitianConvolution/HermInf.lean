import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.NontrivInf

noncomputable section

namespace PositivityTheory.Rg.BcB.F.FBL

def HermInf : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), PositivityTheory.RgBcC.IsHerm (PositivityTheory.RgBcC.infOf lam)

theorem hermInf_holds : HermInf := by
  intro n lam
  refine ⟨Equiv.refl _, fun a => ?_⟩
  simp only [PositivityTheory.RgBcC.infOf, Equiv.refl_apply, Bool.false_eq_true, if_false, if_true, map_mul, map_add, map_sub,
    map_div₀, map_one, map_neg, map_intCast, Complex.conj_natCast, map_ofNat]
  ring

end PositivityTheory.Rg.BcB.F.FBL

end

import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

set_option synthInstance.maxHeartbeats 200000 in
theorem PositivityTheory.NCmp.cap_eq_qdet {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (a : ℕ)
    (τ : E →+* ℂ) (u : ℂ) :
    (GlobalTheory.CuspRep.cap (a := a) τ u : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) =
      Formalism.REAL.qdet (GlobalTheory.CuspRep.Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) :=
  rfl

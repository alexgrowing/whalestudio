import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.XiSchur
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.casXi :
    UpperTheory.V.Lit.Bor.CasXi := by
  intro E _ _ _ a n e he Ξ r
  obtain ⟨h1, h2⟩ := UpperTheory.V.Lit.Bor.xiSchur E a Ξ
  have h3 : IsLieHom (shift Ξ.dmat r) := (UpperTheory.V.Lit.Bor.ellFacts E a).2.2.2 _ _ r h1
  refine h2 _ fun X => ?_
  have h4 := UpperTheory.V.Lit.Bor.casComm E a n e he _ _ h3 X
  rw [shift_apply] at h4
  have h5 : Commute (cas (shift Ξ.dmat r) e) ((r * ell E a X) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)) :=
    (Commute.one_right _).smul_right _
  simpa using h4.sub_right h5

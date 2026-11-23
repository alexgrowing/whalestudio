import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField

namespace GlobalTheory.CompanionTheory.StdCharQ

theorem differentIdeal_rat : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal (K := ℚ), NumberField.discr_rat]
  rfl

theorem differentExp_rat (v : HeightOneSpectrum (𝓞 ℚ)) : differentExp v = 0 := by
  simp only [GroundTheory.Global.differentExp, differentIdeal_rat, FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]

theorem stdChar : Ad3.GP.StdChar := by
  intro v
  unfold Ad3.IsStd Ad3.GP.psiF
  refine ⟨continuous_localAdelicChar v, localAdelicChar_ne_one v, ?_⟩
  rw [addCharConductor_localAdelicChar, differentExp_rat, neg_zero]

end GlobalTheory.CompanionTheory.StdCharQ

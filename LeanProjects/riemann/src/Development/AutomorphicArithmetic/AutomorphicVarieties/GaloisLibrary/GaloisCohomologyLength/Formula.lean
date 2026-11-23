import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.VFormula

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem vFormula_of_classicalTheorems (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) :
    VLen D e + KStar.TotallyRealRoots.nuGal l F e.natAbs = shaLen D e + sumLocalH0TwistLength D e := by
  have hfl := fun r (hr : 0 < r) => GlobalTheory.TateLimit.finite_level D e hP hc r hr
  have hcok := GlobalTheory.TateLimit.ptCokerAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have hsha := GlobalTheory.TateLimit.ptShaAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have h := vFormula F Ω l D e hc hcok hsha (GlobalTheory.TateLimit.local_tate_duality_h2_limit hF hT D e)
  rwa [length_H0_global_eq_nu] at h

theorem ptCase_of_isTotallyComplex (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (l : ℕ) : PTCase F l :=
  Or.inr (NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance)

theorem VLen_le_shaLen_add (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) : VLen D e ≤ shaLen D e + sumLocalH0TwistLength D e := by
  rw [← vFormula_of_classicalTheorems hP hF hT hc]
  exact le_self_add

end

end UpperTheory.V.LDataCardLeFinrank

end

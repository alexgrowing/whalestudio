import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolOfUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolCoeffZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTrivialEverywhere

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne Formalism.CyclotomicNorms

namespace GlobalTheory.LabLaws

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem labTameS_of_labTie {T : GlobalTheory.RowTie.WDTie N A} {τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ}
    {γ : Fin 2 → PlE H → G H.E N.Om} (hT : LabTie T τ γ) : UpperTheory.GalS.LabTameS N A := by
  refine ⟨fun k v a ha σ hσ hw => ?_, fun k v a ha hs hb => ?_⟩
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, ← T.dim] at ha
    rw [T.inePol _ a σ hσ, ← T.dim]
    exact WD.inePol_wild_of_natDegree_lab ha hw
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, ← T.dim] at ha
    rw [(hT k v).2.2] at hs
    refine (UpperTheory.GalS.nc_iff T a).2 (UpperTheory.GalS.SepW.ncW ⟨WD.tame_of_natDegree_lab ha, _, (hT k v).2.1.1, ?_⟩
      (UpperTheory.GalS.thr_split (H.g_prime k) (A.plGw_over k v) (N.g_split k) (by rwa [T.dim])))
    rw [WD.inePol_eq_of_natDegree_lab _ _ _ ha]
    exact GlobalTheory.GoodRowMono.separable_prod_teich _ (hT k v).1 hs

end GlobalTheory.LabLaws

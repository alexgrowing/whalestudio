import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleJOfRestricted
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SemisimpleOfFin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace UpperTheory.GalS

theorem nonCritical_localParam_of_full_dim (D : D7) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (i : D.nd.Loc) (P : D.naut.AV i) (w : PlE D.host) (hw : w ∈ D.nd.S i ∨ w ∈ D.nd.Q i)
    (hA : w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde')))) (hd : D.naut.lpDim (D.naut.locV i P w) = D.R.nV) :
    Nc D.nd D.naut (D.naut.locV i P w) := by
  obtain ⟨hχ, hDel⟩ := (GlobalTheory.T.tame_descent_conditions_every_localisation D i).1
  obtain ⟨m, p⟩ := h4.1 i P w hw (hA.imp id fun h => ⟨hDel, h.2⟩)
  refine ⟨fun σ hσ hW => ?_, m, fun γ hγ z hz => ?_⟩
  · have e : chi1 D.nd i σ = 1 := by
      show ((D.nd.chi i 1 σ : (D.nd.O i)ˣ) : D.nd.O i) = 1
      rw [hχ w hA σ hW, Units.val_one]
    rw [p σ hσ, e, map_one, map_one, ← pow_add, hd]; rfl
  · have h1 : (D.naut.inePol (D.naut.locV i P w) γ).IsRoot z := (rootMultiplicity_pos'.1 (lt_of_lt_of_le (thr_pos w) hz)).2
    rw [p γ hγ.1] at h1
    simp only [IsRoot, eval_mul, eval_pow, eval_sub, eval_X, eval_one, eval_C, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rw [sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1, one_pow]
    · have k := char_pow_ine (D.nd.plOm.2 w) (D.nd.chi i 1) (hχ w hA) γ hγ.1
      rw [sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1, ← map_pow]
      show iotaO D.nd D.naut i (((D.nd.chi i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) ^ _) = 1
      rw [← Units.val_pow_eq_pow_val, k, Units.val_one, map_one]

end UpperTheory.GalS

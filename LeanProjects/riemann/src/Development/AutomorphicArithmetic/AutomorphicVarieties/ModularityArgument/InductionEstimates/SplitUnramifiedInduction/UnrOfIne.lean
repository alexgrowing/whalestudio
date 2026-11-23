import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.SplitOfDecAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationEqOfIneFixes

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.unrOfIne :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.UnrOfIne := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ v hI w
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w.1
  haveI hlo : w.1.asIdeal.LiesOver v.asIdeal := w.2
  have hAv : IsPlaceOver A v := fun x => by
    rw [IsScalarTower.algebraMap_apply K M Ω, Ideal.mem_of_liesOver w.1.asIdeal v.asIdeal x]
    exact hA (algebraMap (𝓞 K) (𝓞 M) x)
  have he := (GlobalTheory.InertFixVal.ramificationIdx_eq_one A v w.1 hAv hA (hI A hAv)).2
  exact Ideal.ramificationIdx_eq_one_iff.1 he

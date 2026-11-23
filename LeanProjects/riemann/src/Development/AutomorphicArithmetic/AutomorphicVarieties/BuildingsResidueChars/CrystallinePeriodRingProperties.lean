import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCharacterRatio

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp

theorem UpperTheory.crystalline_period_ring_properties :
    UpperTheory.V.Af.Wd.BrFacts := by
  classical
  intro F Ω _ _ _ _ _ l _ w A h O _ _ _ Bw hj
  refine ⟨fun c => ?_, fun L s => ?_, fun M hM => ?_⟩
  · have h1 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0) (actsAs_one_iff.2 isFrob_frob) c
    simpa using h1
  · have h2 := GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (UpperTheory.V.Loc.PP l) Bw.j _ _ (Bw.e_comm s)
    exact (congrArg (algebraMap ℚ_[l] (Om l)) h2)
  · have hM0 : M ≠ 0 := by omega
    have hfin : ({x : Om l | x ^ M = 1}).Finite := by
      refine (Polynomial.nthRoots M (1 : Om l)).toFinset.finite_toSet.subset fun x hx => ?_
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hM0)] using hx
    haveI := hfin.to_subtype
    have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ M = 1}) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    refine ⟨⟨_, hfd⟩, fun s hs ζ hζ => Bw.j.injective ?_⟩
    rw [← Bw.e_comm]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs _
      (IntermediateField.subset_adjoin _ _ (show Bw.j ζ ^ M = 1 by rw [← map_pow, hζ, map_one]))

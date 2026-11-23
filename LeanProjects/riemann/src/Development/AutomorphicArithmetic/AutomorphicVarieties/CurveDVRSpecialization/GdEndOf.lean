import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkMarks
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinEndOfFinPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrthogonalPairingFromIntertwiner
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutEnd2OfAutPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IneLeFixingSubgroup

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem fix_iff {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] (hK : Module.finrank ℚ K = 2)
    (f g : K →+* Ω) (s : Ω ≃ₐ[ℚ] Ω) (h : ∀ x, s (f x) = f x) (x : K) : s (g x) = g x := by
  by_cases hq : ∃ q : ℚ, (q : K) = x
  · obtain ⟨q, rfl⟩ := hq
    simp only [map_ratCast]
  · have hli : LinearIndependent ℚ ![(1 : K), x] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      by_cases hb : b = 0
      · subst hb
        simp at hab
        exact ⟨hab, rfl⟩
      · exfalso
        apply hq
        refine ⟨-a / b, ?_⟩
        rw [Rat.smul_def, Rat.smul_def, mul_one] at hab
        have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
        push_cast
        rw [div_eq_iff hb']
        linear_combination -hab
    have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hK])
    have hmem : x * x ∈ Submodule.span ℚ (Set.range ![(1 : K), x]) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Submodule.mem_span_pair] at hmem
    obtain ⟨a, b, hab⟩ := hmem
    rw [Rat.smul_def, Rat.smul_def, mul_one] at hab
    have hg : g x * g x = a + b * g x := by
      rw [← map_mul, ← hab, map_add, map_mul, map_ratCast, map_ratCast]
    have hf : f x * f x = a + b * f x := by
      rw [← map_mul, ← hab, map_add, map_mul, map_ratCast, map_ratCast]
    have hprod : (g x - f x) * (g x - ((b : Ω) - f x)) = 0 := by
      linear_combination hg - hf
    rcases mul_eq_zero.mp hprod with h1 | h1
    · rw [sub_eq_zero.mp h1, h x]
    · have h2 : g x = f ((b : K) - x) := by
        rw [sub_eq_zero.mp h1, map_sub, map_ratCast]
      rw [h2, h]

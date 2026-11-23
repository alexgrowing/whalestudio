import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormMapPowMulPowOfMulConj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem normaliser_factor_mul_bar {D : D7} (EX : ErrX D) (i : Fin 2) :
    EX.piG i * piBarO EX i = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
  apply NumberField.RingOfIntegers.ext
  simpa [piBarO, NumberField.RingOfIntegers.mapRingHom_apply] using EX.piG_norm i

theorem map_piBar_eq_conj {D : D7} (EX : ErrX D) (i : Fin 2) (ρ : 𝓞 D.host.E →+* ℂ)
    (hρ : Function.Injective ρ) : ρ (piBarO EX i) = starRingEnd ℂ (ρ (EX.piG i)) := by
  let ψ : D.host.E →+* ℂ := IsFractionRing.lift hρ
  have hψ : ∀ x : 𝓞 D.host.E, ψ (x : D.host.E) = ρ x := fun x => IsFractionRing.lift_algebraMap hρ x
  rw [← hψ (piBarO EX i), ← hψ (EX.piG i), piBarO, NumberField.RingOfIntegers.mapRingHom_apply]
  exact D.host.toHostAx.conjE_apply ψ _

theorem log_norm_normaliser : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ), nnW B hinj EX w ≠ 0 ∧ Real.log ‖σ (nnW B hinj EX w : B.KO)‖ = (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
  intro D B hinj EX j w σ
  set ρ : 𝓞 D.host.E →+* ℂ := σ.comp ((algebraMap (𝓞 B.KO) B.KO).comp (iE D hinj B)) with hρdef
  have hρ : Function.Injective ρ :=
    σ.injective.comp ((IsFractionRing.injective (𝓞 B.KO) B.KO).comp (iE_injective D hinj B))
  have hg : ∀ i : Fin 2, (0 : ℝ) < (D.host.g i : ℝ) := fun i => by
    exact_mod_cast (D.host.g_prime i).pos
  have hval : σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) =
      ∏ i : Fin 2, ρ (EX.piG i ^ Dplus w * piBarO EX i ^ Dminus w) := by
    simp [nnW, hρdef, map_prod, map_mul, map_pow]
  have hnorm : ‖σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO)‖ =
      ∏ i : Fin 2, (D.host.g i : ℝ) ^ (((Dplus w : ℝ) + Dminus w) / 2) := by
    rw [hval, norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact norm_map_pow_mul_pow_of_mul_conj ρ _ _ _ (normaliser_factor_mul_bar EX i)
      (map_piBar_eq_conj EX i ρ hρ) _ _
  have hDF : WeightAlgebra.DF w = Dplus w + Dminus w := by
    simp only [WeightAlgebra.DF, WeightAlgebra.degP, Dplus, Dminus, Finset.sum_add_distrib]
  have h0 := Real.rpow_pos_of_pos (hg 0) (((Dplus w : ℝ) + Dminus w) / 2)
  have h1 := Real.rpow_pos_of_pos (hg 1) (((Dplus w : ℝ) + Dminus w) / 2)
  refine ⟨fun hz => ?_, ?_⟩
  · have hz' : ‖σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO)‖ = 0 := by rw [hz]; simp
    rw [hnorm, Fin.prod_univ_two] at hz'
    nlinarith [mul_pos h0 h1]
  · rw [hnorm, Fin.prod_univ_two, Real.log_mul h0.ne' h1.ne', Real.log_rpow (hg 0), Real.log_rpow (hg 1),
      Real.log_mul (hg 0).ne' (hg 1).ne', hDF]
    push_cast
    ring

end GlobalTheory

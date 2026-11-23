import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Mathlib.NumberTheory.NumberField.ProductFormula
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

private theorem fin_supp' (y : (Af F)ˣ) : Function.HasFiniteMulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖ := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

private theorem abs_reAt [IsTotallyReal F] (v : InfinitePlace F) (x : F) : |reAt v x| = v x ^ v.mult := by
  have hv : v.IsReal := IsTotallyReal.isReal v
  have hm : v.mult = 1 := by simp [InfinitePlace.mult, hv]
  rw [hm, pow_one, reAt, ← InfinitePlace.norm_embedding_eq, ← InfinitePlace.embedding_of_isReal_apply hv,
    Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]

private theorem absF_rat (x : Fˣ) :
    absF (Units.map (algebraMap F (Af F)).toMonoidHom x) = ∏ᶠ w : FinitePlace F, w (x : F) := by
  unfold absF
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
  refine finprod_congr fun w => ?_
  rfl

end SlopeTestRemainingChoices

theorem UpperTheory.V.Sd.Hm.absf :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
        (∀ y : (Af F)ˣ, 0 < absF y) ∧ (∀ y z : (Af F)ˣ, absF (y * z) = absF y * absF z) ∧
        (∀ u : (Af F)ˣ, (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → absF u = 1) ∧
        ∀ x : Fˣ, (∏ v, |reAt v (x : F)|) * absF (Units.map (algebraMap F (Af F)).toMonoidHom x) = 1 := by
  intro F _ _ _
  refine ⟨fun y => ?_, fun y z => ?_, fun u hu => ?_, fun x => ?_⟩
  · exact finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w =>
      norm_pos_iff.2 (y.isUnit.map (pLoc F w)).ne_zero
  · unfold absF
    rw [← finprod_mul_distrib (fin_supp' y) (fin_supp' z)]
    simp
  · exact finprod_eq_one_of_forall_eq_one fun w => nrm_unit (hu w)
  · rw [absF_rat]
    simp only [abs_reAt]
    exact NumberField.prod_abs_eq_one x.ne_zero

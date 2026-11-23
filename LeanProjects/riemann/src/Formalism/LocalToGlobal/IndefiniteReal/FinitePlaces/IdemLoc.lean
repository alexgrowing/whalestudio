import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem af_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y := by
  first
    | exact RestrictedProduct.ext h
    | exact Subtype.ext (funext h)
    | (ext w
       exact h w)

open Classical in

def sglV (a : v.adicCompletion F) : Af F :=
  ⟨Pi.single v a, by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton v).subset ?_)
    intro w hw
    by_contra hne
    apply hw
    have : w ≠ v := hne
    rw [Pi.single_eq_of_ne this]
    exact zero_mem _⟩

theorem sglV_same (a : v.adicCompletion F) : evalV F v (sglV v a) = a := by
  classical
  first
    | exact Pi.single_eq_same (i := v) (x := a)
    | exact Pi.single_eq_same v a
    | simp [sglV, evalV]

theorem sglV_ne (a : v.adicCompletion F) {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (sglV v a) = 0 := by
  classical
  first
    | exact Pi.single_eq_of_ne h a
    | exact Pi.single_eq_of_ne (i := v) h a
    | simp [sglV, evalV, h]

theorem sglV_add (a b : v.adicCompletion F) : sglV v (a + b) = sglV v a + sglV v b := by
  refine af_ext fun w => ?_
  rw [map_add]
  by_cases h : w = v
  · subst h
    rw [sglV_same, sglV_same, sglV_same]
  · rw [sglV_ne _ _ h, sglV_ne _ _ h, sglV_ne _ _ h, add_zero]

theorem sglV_mul (a b : v.adicCompletion F) : sglV v (a * b) = sglV v a * sglV v b := by
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases h : w = v
  · subst h
    rw [sglV_same, sglV_same, sglV_same]
  · rw [sglV_ne _ _ h, sglV_ne _ _ h, sglV_ne _ _ h, mul_zero]

theorem sglV_zero : sglV v (0 : v.adicCompletion F) = 0 := by
  refine af_ext fun w => ?_
  rw [map_zero]
  by_cases h : w = v
  · subst h
    rw [sglV_same]
  · rw [sglV_ne _ _ h]

theorem sglV_smul (f : F) (a : v.adicCompletion F) :
    algebraMap F (Af F) f * sglV v a = sglV v (algebraMap F (v.adicCompletion F) f * a) := by
  refine af_ext fun w => ?_
  rw [map_mul, AlgHom.commutes]
  by_cases h : w = v
  · subst h
    rw [sglV_same, sglV_same] <;> rfl
  · rw [sglV_ne _ _ h, sglV_ne _ _ h, mul_zero]

theorem sglV_int {a : v.adicCompletion F} (ha : a ∈ v.adicCompletionIntegers F) : sglV v a ∈ intAf F := by
  first
    | (intro w
       by_cases h : w = v
       · subst h
         rw [sglV_same]
         exact ha
       · rw [sglV_ne _ _ h]
         exact zero_mem _)
    | (intro w
       by_cases h : w = v
       · subst h
         show evalV F w (sglV w a) ∈ _
         rw [sglV_same]
         exact ha
       · show evalV F w (sglV v a) ∈ _
         rw [sglV_ne _ _ h]
         exact zero_mem _)

def sA : v.adicCompletion F →ₙ+* AF F where
  toFun a := pairA F 0 (sglV v a)
  map_mul' a b := Prod.ext (by show (0 : Ainf F) = 0 * 0; rw [mul_zero]) (sglV_mul v a b)
  map_zero' := Prod.ext rfl (sglV_zero v)
  map_add' a b := Prod.ext (by show (0 : Ainf F) = 0 + 0; rw [add_zero]) (sglV_add v a b)

theorem sA_smul (f : F) (a : v.adicCompletion F) :
    algebraMap F (AF F) f * sA v a = sA v (algebraMap F (v.adicCompletion F) f * a) := by
  first
    | exact Prod.ext (mul_zero _) (sglV_smul v f a)
    | (refine Prod.ext ?_ ?_
       · show _ * (0 : Ainf F) = 0
         exact mul_zero _
       · exact sglV_smul v f a)

theorem sA_one_mul (a : AF F) : sA v 1 * a = sA v (evalV F v (sndA F a)) := by
  refine Prod.ext ?_ ?_
  · show (0 : Ainf F) * _ = 0
    exact zero_mul _
  · show sglV v 1 * _ = sglV v _
    refine af_ext fun w => ?_
    rw [map_mul]
    by_cases h : w = v
    · subst h
      rw [sglV_same, sglV_same, one_mul] <;> rfl
    · rw [sglV_ne _ _ h, sglV_ne _ _ h, zero_mul]

theorem mem_O_of_integral {y : v.adicCompletion F} (hy : IsIntegral ℤ y) : Valued.v y ≤ 1 := by
  first
    | (have hm := (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).mem_of_integral
         (IsIntegral.tower_top hy)
       first
         | exact hm
         | (obtain ⟨o, rfl⟩ := hm
            exact o.2)
         | (rcases hm with ⟨o, ho⟩
            rw [← ho]
            exact o.2))
    | (have hm := Valuation.Integers.mem_of_integral (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _))
         (IsIntegral.tower_top (A := (Valued.v : Valuation (v.adicCompletion F) _).integer) hy)
       first
         | exact hm
         | (obtain ⟨o, rfl⟩ := hm
            exact o.2))

theorem val_coe_lt_one_iff (f : 𝓞 F) :
    Valued.v (((f : F) : v.adicCompletion F)) < 1 ↔ f ∈ v.asIdeal := by
  have e : Valued.v (((f : F) : v.adicCompletion F)) = v.intValuation f := by
    first
      | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
         exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (r := f))
      | simp [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [e]
  first
    | exact IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v f
    | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd v f).trans Ideal.dvd_span_singleton
    | (rw [IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton])

theorem val_coe_le_one (f : 𝓞 F) : Valued.v (((f : F) : v.adicCompletion F)) ≤ 1 := by
  first
    | exact mem_O_of_integral v ((NumberField.RingOfIntegers.isIntegral_coe f).map (algebraMap F (v.adicCompletion F)).toIntAlgHom)
    | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
         ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (r := f) ▸ rfl]
       exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v f)
    | (have e : Valued.v (((f : F) : v.adicCompletion F)) = v.intValuation f := by
         rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
         exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (r := f)
       rw [e]
       exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v f)

set_option maxHeartbeats 800000 in

theorem roots_exist (t N : 𝓞 F) (hN : N ∈ v.asIdeal) (ht : t ∉ v.asIdeal) :
    ∃ r₁ r₂ : v.adicCompletion F, r₁ + r₂ = ((t : F) : v.adicCompletion F) ∧ r₁ * r₂ = ((N : F) : v.adicCompletion F) ∧
      Valued.v r₁ < 1 ∧ Valued.v r₂ = 1 := by
  haveI : HenselianLocalRing (v.adicCompletionIntegers F) := inferInstance
  have hI : (Valued.v : Valuation (v.adicCompletion F) _).Integers (v.adicCompletionIntegers F) :=
    ⟨Subtype.val_injective, fun x => x.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  have ea : ∀ x : v.adicCompletionIntegers F, algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) x = (x : v.adicCompletion F) := fun x => rfl
  have hnu : ∀ x : v.adicCompletionIntegers F, ¬ IsUnit x ↔ Valued.v (x : v.adicCompletion F) < 1 := by
    intro x
    have hle := hI.map_le_one x
    rw [ea] at hle
    rw [hI.isUnit_iff_valuation_eq_one, ea]
    exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
  have ht1 : Valued.v (((t : F) : v.adicCompletion F)) = 1 :=
    le_antisymm (val_coe_le_one v t) (not_lt.1 fun h => ht ((val_coe_lt_one_iff v t).1 h))
  have hN1 : Valued.v (((N : F) : v.adicCompletion F)) < 1 := (val_coe_lt_one_iff v N).2 hN
  obtain ⟨t', ht'⟩ : ∃ t' : v.adicCompletionIntegers F, (t' : v.adicCompletion F) = ((t : F) : v.adicCompletion F) := ⟨⟨_, val_coe_le_one v t⟩, rfl⟩
  obtain ⟨N', hN'⟩ : ∃ N' : v.adicCompletionIntegers F, (N' : v.adicCompletion F) = ((N : F) : v.adicCompletion F) := ⟨⟨_, val_coe_le_one v N⟩, rfl⟩
  have hmon : (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N').Monic := by
    first
      | monicity!
      | exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one 2 (by compute_degree!) (by simp)
  have he0 : Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N') = N' := by simp
  have h0 : Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N') ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [he0, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hnu, hN']
    exact hN1
  have hd0 : Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N')) = -t' := by simp
  have hu : IsUnit (Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N'))) := by
    rw [hd0]
    refine IsUnit.neg ?_
    rw [hI.isUnit_iff_valuation_eq_one, ea, ht']
    exact ht1
  obtain ⟨a, ha, ha0⟩ := HenselianLocalRing.is_henselian _ hmon 0 h0 hu
  have ha1 : Valued.v (a : v.adicCompletion F) < 1 := by
    have h4 := ha0
    rw [sub_zero, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hnu] at h4
    exact h4
  have h2 : (a : v.adicCompletion F) ^ 2 - ((t : F) : v.adicCompletion F) * a + ((N : F) : v.adicCompletion F) = 0 := by
    have ha' : Polynomial.eval a (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N') = 0 := ha
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] at ha'
    have h3 := congrArg (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) ha'
    push_cast at h3
    rw [ht', hN'] at h3
    exact h3
  refine ⟨(a : v.adicCompletion F), ((t : F) : v.adicCompletion F) - a, by ring, by linear_combination -h2, ha1, ?_⟩
  first
    | rw [Valuation.map_sub_eq_of_lt_left _ (by rw [ht1]; exact ha1), ht1]
    | rw [Valuation.map_sub_eq_of_lt_right _ (by rw [ht1]; exact ha1), ht1]

end Loc

end Formalism.IndefR.Fin

end

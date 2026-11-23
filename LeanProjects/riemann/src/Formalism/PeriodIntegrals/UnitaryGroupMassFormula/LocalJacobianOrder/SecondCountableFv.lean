import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianOrder.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianOrder.AbsVNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical

def BoxScale : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (ι : Type) [Fintype ι], Module.finrank F E = 2 →
    ∀ (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure] (x : ι → Fv F v), (∀ i, x i ≠ 0) →
      (μ (Set.univ.pi fun i => {c | sc (E := E) v (x i) * c ∈ OEv (E := E) v})).toReal =
        (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (x i) ^ 2)⁻¹

def AbsMul : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
    (∀ x y : Fv F v, absV v (x * y) = absV v x * absV v y) ∧ absV v 1 = 1 ∧
      ∀ x : Fv F v, x ≠ 0 → 0 < absV v x

section Top

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem secondCountable_Fv : SecondCountableTopology (Fv F v) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
  exact UniformSpace.secondCountable_of_separable (Fv F v)

theorem locallyCompact_Fv : LocallyCompactSpace (Fv F v) :=
  (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))

end Top

theorem absMul_holds : AbsMul := fun v => ⟨Ar.absV_mul v, Ar.absV_one v, fun x hx => by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  simp only [absV, dif_neg hx']
  exact zpow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ar.absNorm_ne_zero v).symm) _⟩

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem alp_ne_zero (r : ℕ) (a : Fin (r + 1)) : alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

theorem absV_inv (hA : AbsMul) (x : Fv F v) (hx : x ≠ 0) : absV v x⁻¹ = (absV v x)⁻¹ := by
  obtain ⟨hm, h1, hp⟩ := hA v
  have : absV v x⁻¹ * absV v x = 1 := by rw [← hm, inv_mul_cancel₀ hx, h1]
  exact eq_inv_of_mul_eq_one_left this

theorem absV_pow (hA : AbsMul) (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  obtain ⟨hm, h1, hp⟩ := hA v
  induction n with
  | zero => simp [h1]
  | succ n ih => rw [pow_succ, hm, ih, pow_succ]

theorem volZZO_of (hB : BoxScale) (hA : AbsMul) : VolZZO (E := E) v := by
  intro r m hfin μ hμ hO
  have hset : ZZOrd (E := E) v r =
      Set.univ.pi fun p : Fin (r + 1) × Fin (r + 1) =>
        {c | sc (E := E) v (alp v r p.1 * alp v r p.2) * c ∈ OEv (E := E) v} := by
    ext z
    simp [ZZOrd, locZ, Set.mem_pi, Prod.forall]
  rw [hset, hB v _ hfin μ (fun p => alp v r p.1 * alp v r p.2)
    (fun p => mul_ne_zero (alp_ne_zero v r p.1) (alp_ne_zero v r p.2)), hO,
    Fintype.prod_prod_type]
  simp only [(hA v).1]

theorem volUO_of (hB : BoxScale) (hA : AbsMul) : VolUO (E := E) v := by
  intro r m hfin μ hμ hO
  have hset : UO (E := E) v r =
      Set.univ.pi fun q : UIdx r =>
        {c | sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2) * c ∈ OEv (E := E) v} := by
    ext z
    simp [UO, Set.mem_pi]
  have e1 := hB v (UIdx r) hfin μ (fun q => (alp v r q.1.1)⁻¹ * alp v r q.1.2)
    (fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v r q.1.1)) (alp_ne_zero v r q.1.2))
  rw [← hset, hO] at e1
  have : SecondCountableTopology (Fv F v) := secondCountable_Fv F v
  have : LocallyCompactSpace (Fv F v) := locallyCompact_Fv F v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  unfold localVolumeOrdinary
  rw [Measure.prod_prod, ENNReal.toReal_mul, e1, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [(hA v).1, absV_inv v hA _ (alp_ne_zero v r q.1.1)]
  simp only [mul_inv, inv_pow, inv_inv, div_eq_mul_inv, mul_pow]
  ring

theorem volPO_of (hB : BoxScale) (hA : AbsMul) : VolPO (E := E) v := by
  intro r m hfin μ hμ hO l
  have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPOrd (E := E) v r l =
      Set.univ.pi fun _ : Unit => {c | sc (E := E) v (alp v r l ^ 2) * c ∈ OEv (E := E) v} := by
    ext z
    simp only [PPOrd, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    exact ⟨fun h _ => h, fun h => h ()⟩
  rw [hset, hB v Unit hfin μ (fun _ => alp v r l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v r l)), hO]
  simp only [Finset.univ_unique, Finset.prod_singleton, absV_pow v hA]
  ring

end

end PI.LocJacOrd.W

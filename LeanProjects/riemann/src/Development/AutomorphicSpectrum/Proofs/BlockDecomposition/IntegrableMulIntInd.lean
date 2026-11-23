import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.NormGauss

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep

section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem ord_unif : ord (unifUnit K : K) = 1 := (exists_units_ord_eq_one K).choose_spec

theorem mem_int_iff_ord {x : K} (hx : x ≠ 0) : x ∈ 𝒪[K] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hx]

end

section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open Classical in

def uInd (x : K) : ℂ := if modulus x = 1 then 1 else 0

theorem intInd_of_mem {x : K} (h : x ∈ 𝒪[K]) : intInd x = 1 := by simp [intInd, h]

theorem intInd_of_not_mem {x : K} (h : x ∉ 𝒪[K]) : intInd x = 0 := by simp [intInd, h]

theorem modulus_eq_one_iff {x : K} (hx : x ≠ 0) : modulus x = 1 ↔ ord x = 0 := by
  rw [modulus_of_ne_zero hx]
  have hq : (1 : NNReal) < (residueCard K : NNReal) := one_lt_residueCard_nnreal
  constructor
  · intro h
    have := (zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne') (h.trans (zpow_zero _).symm)
    omega
  · intro h
    rw [h, neg_zero, zpow_zero]

theorem intInd_split {c : K} (hc : ord c = 1) (x : K) : intInd x = uInd x + intInd (c⁻¹ * x) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [ord_zero] at hc
    omega
  rcases eq_or_ne x 0 with rfl | h0
  · simp [uInd, intInd, zero_mem]
  have hm : c⁻¹ * x ≠ 0 := mul_ne_zero (inv_ne_zero hc0) h0
  have ho : ord (c⁻¹ * x) = ord x - 1 := by
    rw [ord_mul (inv_ne_zero hc0) h0, ord_inv hc0, hc]
    ring
  by_cases hx : ord x = 0
  · rw [intInd_of_mem ((mem_int_iff_ord h0).2 hx.ge),
      intInd_of_not_mem (fun h => by have := (mem_int_iff_ord hm).1 h; omega)]
    simp [uInd, (modulus_eq_one_iff h0).2 hx]
  · have hu : uInd x = 0 := by simp [uInd, (modulus_eq_one_iff h0).not.2 hx]
    rw [hu, zero_add]
    by_cases hp : 0 < ord x
    · rw [intInd_of_mem ((mem_int_iff_ord h0).2 hp.le), intInd_of_mem ((mem_int_iff_ord hm).2 (by omega))]
    · rw [intInd_of_not_mem (fun h => by have := (mem_int_iff_ord h0).1 h; omega),
        intInd_of_not_mem (fun h => by have := (mem_int_iff_ord hm).1 h; omega)]

variable [MeasurableSpace K] [BorelSpace K]

theorem intInd_eq_indicator : (intInd : K → ℂ) = (valBall K 0 : Set K).indicator fun _ => 1 := by
  funext x
  by_cases h : x ∈ 𝒪[K]
  · rw [intInd_of_mem h, Set.indicator_of_mem (show x ∈ (valBall K 0 : Set K) from mem_valBall_zero_iff.2 h)]
  · rw [intInd_of_not_mem h, Set.indicator_of_notMem (show x ∉ (valBall K 0 : Set K) from fun h' => h (mem_valBall_zero_iff.1 h'))]

theorem integrable_intInd : Integrable (intInd : K → ℂ) (haarIntegers K) := by
  rw [intInd_eq_indicator]
  refine (integrable_indicator_iff (measurableSet_valBall 0)).2 ?_
  refine integrableOn_const ?_
  exact (isCompact_valBall 0).measure_lt_top.ne

theorem integral_intInd : ∫ x, (intInd x : ℂ) ∂haarIntegers K = 1 := by
  rw [intInd_eq_indicator, integral_indicator (measurableSet_valBall 0)]
  simp [measureReal_def, coe_valBall_zero, haarIntegers_integers]

theorem integrable_mul_intInd {f : K → ℂ} (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ 1) :
    Integrable (fun x => f x * intInd x) (haarIntegers K) :=
  (integrable_intInd (K := K)).bdd_mul hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]

theorem ramIdx_eq_one (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) : ramificationIndex F E = 1 := by
  have h := ord_algebraMap (K := F) (L := E) (unifUnit F : F)
  rw [h1, ord_unif] at h
  omega

theorem resDeg_eq_two (hd : Module.finrank F E = 2) (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) :
    residueDegree F E = 2 := by
  have h := ramificationIndex_mul_residueDegree F E
  rw [ramIdx_eq_one h1, hd] at h
  omega

theorem ord_map (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) (a : F) :
    ord (algebraMap F E a) = ord a := by
  rw [ord_algebraMap, ramIdx_eq_one h1]; simp

theorem ord_normE (hd : Module.finrank F E = 2) (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) (x : E) :
    ord (Algebra.norm F x) = 2 * ord x := by
  rw [ord_norm, resDeg_eq_two hd h1]; simp

theorem card_E (hd : Module.finrank F E = 2) (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) :
    residueCard E = residueCard F ^ 2 := by
  have h := card_residueField_eq_pow_residueDegree F E
  rw [resDeg_eq_two hd h1] at h
  exact h

theorem norm_mem {u : E} (hu : u ∈ 𝒪[E]) : Algebra.norm F u ∈ 𝒪[F] := by
  rcases eq_or_ne u 0 with rfl | h0
  · rw [Algebra.norm_zero]
    exact zero_mem _
  · have hN : Algebra.norm F u ≠ 0 := Algebra.norm_ne_zero_iff.2 h0
    rw [mem_int_iff_ord hN, ord_norm]
    have := (mem_int_iff_ord h0).1 hu
    positivity

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [hE : Fact (Module.finrank F E = 2)]

theorem map_mem_valBall_iff (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {n : ℤ} {a : F} :
    algebraMap F E a ∈ valBall E n ↔ a ∈ valBall F n := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [map_zero, zero_mem]
  have ha' : algebraMap F E a ≠ 0 := by simpa using ha
  rw [mem_valBall_iff_le_ord ha, mem_valBall_iff_le_ord ha', ord_map h1]

theorem trace_mem_valBall (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {n : ℤ} {x : E}
    (hx : x ∈ valBall E n) : Algebra.trace F E x ∈ valBall F n := by
  rw [← map_mem_valBall_iff (E := E) h1, algebraMap_trace_eq_add_conj]
  exact add_mem hx (conj_mem_valBall_iff.2 hx)

theorem trace_mem (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {u : E} (hu : u ∈ 𝒪[E]) :
    Algebra.trace F E u ∈ 𝒪[F] :=
  mem_valBall_zero_iff.1 (trace_mem_valBall h1 (mem_valBall_zero_iff.2 hu))

theorem continuous_trace' (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) :
    Continuous (Algebra.trace F E) := by
  have ht : Filter.Tendsto (Algebra.trace F E) (nhds 0) (nhds 0) :=
    ((hasBasis_nhds_zero_valBall (K := E)).tendsto_iff (hasBasis_nhds_zero_valBall (K := F))).2
      fun n _ => ⟨n, trivial, fun x hx => trace_mem_valBall h1 hx⟩
  refine continuous_of_continuousAt_zero (Algebra.trace F E).toAddMonoidHom ?_
  simpa [ContinuousAt] using ht

theorem continuous_norm' (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) :
    Continuous (Algebra.norm F : E → F) := by
  have ht : Filter.Tendsto (Algebra.norm F : E → F) (nhds 0) (nhds 0) := by
    refine ((hasBasis_nhds_zero_valBall (K := E)).tendsto_iff (hasBasis_nhds_zero_valBall (K := F))).2
      fun n _ => ⟨max n 0, trivial, fun x hx => ?_⟩
    rcases eq_or_ne x 0 with rfl | h0
    · rw [Algebra.norm_zero]
      exact zero_mem _
    have hN : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.2 h0
    have hx' := (mem_valBall_iff_le_ord h0).1 hx
    have := ord_normE hE.out h1 x
    show Algebra.norm F x ∈ valBall F n
    rw [mem_valBall_iff_le_ord hN, this]
    omega
  rw [continuous_iff_continuousAt]
  intro x
  have e : (Algebra.norm F : E → F) = fun z => Algebra.norm F x + Algebra.norm F (z - x) +
      Algebra.trace F E (x * conj F E (z - x)) := by
    funext z
    have := norm_add (K := F) x (z - x)
    rwa [add_sub_cancel] at this
  rw [e]
  have c1 : ContinuousAt (fun z : E => Algebra.norm F (z - x)) x := by
    have h0 : Continuous (fun z : E => z - x) := continuous_id'.sub continuous_const
    have h2 := h0.tendsto x
    simp only [sub_self] at h2
    have hz : Algebra.norm F (x - x) = 0 := by rw [sub_self, Algebra.norm_zero]
    show Filter.Tendsto _ _ (nhds (Algebra.norm F (x - x)))
    rw [hz]
    exact ht.comp h2
  have c2 : Continuous (fun z : E => Algebra.trace F E (x * conj F E (z - x))) :=
    (continuous_trace' h1).comp (continuous_const.mul (continuous_conj.comp (continuous_id.sub continuous_const)))
  exact (continuousAt_const.add c1).add c2.continuousAt

end
end GlobalTheory.CompanionTheory.NormGauss

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulIntInd
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.NormGauss

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep Ad3.K.GL2LocalData

section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem char_int {χ : AddChar K Circle} (hχ : IsStd χ) {a : K} (ha : a ∈ 𝒪[K]) : χ a = 1 := by
  have := isTrivialOn_addCharConductor hχ.1 hχ.2.1
  rw [hχ.2.2] at this
  exact this a (mem_valBall_zero_iff.2 ha)

theorem intInd_add_of_mem {b : K} (hb : b ∈ 𝒪[K]) (u : K) : intInd (u + b) = intInd u := by
  by_cases hu : u ∈ 𝒪[K]
  · rw [intInd_of_mem hu, intInd_of_mem (add_mem hu hb)]
  · rw [intInd_of_not_mem hu, intInd_of_not_mem (fun h => hu (by simpa using sub_mem h hb))]

variable [MeasurableSpace K] [BorelSpace K]

theorem selfDual_std {ψ : AddChar K Circle} (hψ : IsStd ψ) : GroundTheory.LocalField.selfDualMeasure ψ = haarIntegers K := by
  unfold GroundTheory.LocalField.selfDualMeasure
  rw [hψ.2.2]
  simp

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [hE : Fact (Module.finrank F E = 2)]

variable (E) in

def gInt (χ : AddChar F Circle) (δ : F) (y : E) : ℂ :=
  ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂haarIntegers E

theorem gInt_of_mem {χ : AddChar F Circle} (hχ : IsStd χ) (hχE : IsStd (chE E χ)) {δ : F} (hδ : δ ∈ 𝒪[F])
    (y : E) : gInt E χ δ y = intInd y := by
  have key := localFourier_indicator_valBall (haarIntegers E) hχE.1 hχE.2.1 0 (-y)
  unfold localFourier at key
  rw [hχE.2.2, sub_zero, ← intInd_eq_indicator] at key
  have e : ∀ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u =
      intInd u * ((chE E χ) (u * -y) : ℂ) := by
    intro u
    by_cases hu : u ∈ 𝒪[E]
    · have h2 : δ * Algebra.norm F u - Algebra.trace F E (y * u) =
          δ * Algebra.norm F u + Algebra.trace F E (u * -y) := by
        rw [sub_eq_add_neg, ← map_neg]
        congr 2
        ring
      rw [h2, AddChar.map_add_eq_mul, char_int hχ (mul_mem hδ (norm_mem hu)), one_mul, mul_comm]
      rfl
    · simp [intInd_of_not_mem hu]
  have i1 : intInd (-y) = intInd y := by
    by_cases hy : y ∈ 𝒪[E]
    · rw [intInd_of_mem hy, intInd_of_mem (neg_mem hy)]
    · rw [intInd_of_not_mem hy, intInd_of_not_mem (fun h => hy (by simpa using neg_mem h))]
  unfold gInt
  simp_rw [e]
  rw [key, i1]
  simp [measureReal_def, coe_valBall_zero, haarIntegers_integers]

theorem gInt_shift (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) (χ : AddChar F Circle) {δ : F} (hδ : δ ≠ 0) {y : E}
    (hy : y * algebraMap F E δ⁻¹ ∈ 𝒪[E]) :
    gInt E χ δ y = (χ (-(Algebra.norm F y) / δ) : ℂ) * gInt E χ δ 0 := by
  have hD : algebraMap F E δ ≠ 0 := by simpa using hδ
  set b : E := conj F E y * algebraMap F E δ⁻¹ with hb
  have hbO : b ∈ 𝒪[E] := by
    have : conj F E (y * algebraMap F E δ⁻¹) = b := by simp [hb]
    rw [← this]
    exact mem_valBall_zero_iff.1 (conj_mem_valBall_iff.2 (mem_valBall_zero_iff.2 hy))
  have ident : ∀ u : E, δ * Algebra.norm F u - Algebra.trace F E (y * u) =
      δ * Algebra.norm F (u - b) + -(Algebra.norm F y) / δ := by
    intro u
    apply (algebraMap F E).injective
    simp only [map_add, map_sub, map_mul, map_div₀, map_neg, algebraMap_norm_eq_mul_conj, algebraMap_trace_eq_add_conj, hb,
      conj_conj, conj_algebraMap, map_inv₀]
    field_simp
    ring
  unfold gInt
  simp_rw [ident, AddChar.map_add_eq_mul]
  have e2 : ∀ u : E, ((χ (δ * Algebra.norm F (u - b)) * χ (-(Algebra.norm F y) / δ) : Circle) : ℂ) * intInd u =
      (χ (-(Algebra.norm F y) / δ) : ℂ) * ((χ (δ * Algebra.norm F (u - b)) : ℂ) * intInd (u - b + b)) := by
    intro u
    rw [sub_add_cancel]
    push_cast
    ring
  simp_rw [e2]
  rw [integral_const_mul]
  congr 1
  rw [integral_sub_right_eq_self (fun x => (χ (δ * Algebra.norm F x) : ℂ) * intInd (x + b)) b]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [intInd_add_of_mem hbO, zero_mul, map_zero, sub_zero]

theorem gInt_eq_zero (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {χ : AddChar F Circle} (hχ : IsStd χ) (hχE : IsStd (chE E χ)) {δ : F} (hδ : δ ∉ 𝒪[F]) {y : E}
    (hy : y * algebraMap F E δ⁻¹ ∉ 𝒪[E]) : gInt E χ δ y = 0 := by
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hδ (zero_mem _)
  have hD : algebraMap F E δ ≠ 0 := by simpa using hδ0
  have hinv : δ⁻¹ ∈ 𝒪[F] := by
    rw [mem_int_iff_ord (inv_ne_zero hδ0), ord_inv hδ0]
    have := (mem_int_iff_ord hδ0).not.1 hδ
    omega
  set y' : E := y * algebraMap F E δ⁻¹ with hy'
  obtain ⟨a, haO, hc⟩ : ∃ a : E, a ∈ 𝒪[E] ∧ χ (Algebra.trace F E (a * y')) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have := (forall_integer_mul_eq_one_iff hχE.1 hχE.2.1 y').1 (fun a ha => hcon a ha)
    rw [hχE.2.2] at this
    exact hy (mem_valBall_zero_iff.1 this)
  set v : E := a * algebraMap F E δ⁻¹ with hv
  have hvO : v ∈ 𝒪[E] := mul_mem haO ((algebraMap_mem_integer_iff F E _).2 hinv)
  set f : E → ℂ := fun u => (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u with hf
  have ident : ∀ u : E, δ * Algebra.norm F (u + v) - Algebra.trace F E (y * (u + v)) =
      (δ * Algebra.norm F u - Algebra.trace F E (y * u)) + Algebra.trace F E (u * conj F E a) +
        Algebra.norm F a * δ⁻¹ + -Algebra.trace F E (a * y') := by
    intro u
    apply (algebraMap F E).injective
    simp only [map_add, map_sub, map_mul, map_neg, algebraMap_norm_eq_mul_conj, algebraMap_trace_eq_add_conj, hv, hy',
      conj_conj, conj_algebraMap, map_inv₀]
    field_simp
    ring
  have hsh : ∀ u : E, f (u + v) = ((χ (Algebra.trace F E (a * y')) : ℂ))⁻¹ * f u := by
    intro u
    simp only [hf, intInd_add_of_mem hvO]
    by_cases hu : u ∈ 𝒪[E]
    · rw [ident, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
        char_int hχ (trace_mem h1 (mul_mem hu ?_)), char_int hχ (mul_mem (norm_mem haO) hinv), AddChar.map_neg_eq_inv]
      · push_cast
        simp
        ring
      · exact mem_valBall_zero_iff.1 (conj_mem_valBall_iff.2 (mem_valBall_zero_iff.2 haO))
    · simp [intInd_of_not_mem hu]
  have h3 : gInt E χ δ y = ((χ (Algebra.trace F E (a * y')) : ℂ))⁻¹ * gInt E χ δ y := by
    show ∫ u, f u ∂haarIntegers E = _ * ∫ u, f u ∂haarIntegers E
    rw [← integral_const_mul, ← integral_add_right_eq_self f v]
    exact integral_congr_ae (Filter.Eventually.of_forall hsh)
  have hne : ((χ (Algebra.trace F E (a * y')) : ℂ))⁻¹ ≠ 1 := by
    intro h
    apply hc
    have : (χ (Algebra.trace F E (a * y')) : ℂ) = 1 := by simpa using h
    exact Circle.ext (by simpa using this)
  by_contra h0
  exact hne (mul_right_cancel₀ h0 (by rw [one_mul]; exact h3.symm))

end

section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem cont_circ {X : Type} [TopologicalSpace X] {g : X → Circle} (hg : Continuous g) :
    Continuous fun x => (g x : ℂ) := by
  first | fun_prop | exact continuous_subtype_val.comp hg | exact continuous_induced_dom.comp hg

theorem integrable_intInd_mul {c : K} (hc : c ≠ 0) :
    Integrable (fun x => (intInd (c * x) : ℂ)) (haarIntegers K) := by
  have he : MeasurableEmbedding (fun x : K => c * x) := (Homeomorph.mulLeft₀ c hc).measurableEmbedding
  have h : Integrable (intInd : K → ℂ) (Measure.map (fun x => c * x) (haarIntegers K)) := by
    rw [map_mul_left_eq_smul _ hc]
    exact (integrable_intInd (K := K)).smul_measure_nnreal
  exact (he.integrable_map_iff).1 h

theorem uInd_eq {c : K} (hc : ord c = 1) (x : K) : uInd x = intInd x - intInd (c⁻¹ * x) := by
  rw [intInd_split hc x]
  ring

theorem ne_zero_of_ord {c : K} (hc : ord c = 1) : c ≠ 0 := by
  rintro rfl
  rw [ord_zero] at hc
  omega

theorem integrable_uInd : Integrable (uInd : K → ℂ) (haarIntegers K) := by
  have h : (uInd : K → ℂ) = fun x => intInd x - intInd ((unifUnit K : K)⁻¹ * x) :=
    funext (uInd_eq ord_unif)
  rw [h]
  exact integrable_intInd.sub (integrable_intInd_mul (inv_ne_zero (unifUnit K).ne_zero))

theorem four_int {χ : AddChar K Circle} (hχ : IsStd χ) (a : K) :
    ∫ x, (χ (a * x) : ℂ) * intInd x ∂haarIntegers K = intInd a := by
  have key := localFourier_indicator_valBall (haarIntegers K) hχ.1 hχ.2.1 0 a
  unfold localFourier at key
  rw [hχ.2.2, sub_zero, ← intInd_eq_indicator] at key
  have e : ∀ x : K, (χ (a * x) : ℂ) * intInd x = intInd x * (χ (x * a) : ℂ) := fun x => by
    rw [mul_comm a x, mul_comm]
  simp_rw [e]
  rw [key]
  simp [measureReal_def, coe_valBall_zero, haarIntegers_integers]

theorem modulus_unif : modulus (unifUnit K : K) = (residueCard K : NNReal)⁻¹ := by
  rw [modulus_of_ne_zero (unifUnit K).ne_zero, ord_unif, zpow_neg, zpow_one]

theorem uAvg {χ : AddChar K Circle} (hχ : IsStd χ) (a : K) :
    ∫ x, (χ (a * x) : ℂ) * uInd x ∂haarIntegers K =
      intInd a - (residueCard K : ℂ)⁻¹ * intInd ((unifUnit K : K) * a) := by
  set c : K := (unifUnit K : K) with hc
  have hc0 : c ≠ 0 := (unifUnit K).ne_zero
  have hcont : Continuous fun x : K => (χ (a * x) : ℂ) :=
    cont_circ (hχ.1.comp (continuous_const.mul continuous_id))
  have i1 := integrable_mul_intInd hcont (fun x => (Circle.norm_coe _).le)
  have i2 : Integrable (fun x => (χ (a * x) : ℂ) * intInd (c⁻¹ * x)) (haarIntegers K) :=
    (integrable_intInd_mul (inv_ne_zero hc0)).bdd_mul hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (Circle.norm_coe _).le)
  have e : ∀ x, (χ (a * x) : ℂ) * uInd x = (χ (a * x) : ℂ) * intInd x - (χ (a * x) : ℂ) * intInd (c⁻¹ * x) := by
    intro x
    rw [uInd_eq ord_unif x]
    ring
  simp_rw [e]
  rw [integral_sub i1 i2, four_int hχ]
  have h3 := integral_comp_mul_left (haarIntegers K) (inv_ne_zero hc0)
    (fun x => (χ (a * (c * x)) : ℂ) * intInd x)
  have e3 : ∀ x, (χ (a * (c * (c⁻¹ * x))) : ℂ) * intInd (c⁻¹ * x) = (χ (a * x) : ℂ) * intInd (c⁻¹ * x) := by
    intro x
    rw [mul_inv_cancel_left₀ hc0]
  simp_rw [e3] at h3
  rw [h3]
  have e4 : ∀ x, (χ (a * (c * x)) : ℂ) * intInd x = (χ ((c * a) * x) : ℂ) * intInd x := by
    intro x
    congr 3
    ring
  simp_rw [e4]
  rw [four_int hχ, modulus_inv, modulus_unif]
  simp

theorem integral_uInd {χ : AddChar K Circle} (hχ : IsStd χ) :
    ∫ x, (uInd x : ℂ) ∂haarIntegers K = 1 - (residueCard K : ℂ)⁻¹ := by
  have h := uAvg hχ 0
  simp only [zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, mul_zero] at h
  rw [h, intInd_of_mem (zero_mem _)]
  ring

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [hE : Fact (Module.finrank F E = 2)]

variable (E) in

def hInt (χ : AddChar F Circle) (δ : F) : ℂ :=
  ∫ u : E, (χ (δ * Algebra.norm F u) : ℂ) * uInd u ∂haarIntegers E

theorem cont_chiN (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {χ : AddChar F Circle} (hχ : IsStd χ) (δ : F) :
    Continuous fun u : E => (χ (δ * Algebra.norm F u) : ℂ) :=
  cont_circ (hχ.1.comp (continuous_const.mul (continuous_norm' h1)))

theorem gInt_zero_eq (χ : AddChar F Circle) (δ : F) :
    gInt E χ δ 0 = ∫ u : E, (χ (δ * Algebra.norm F u) : ℂ) * intInd u ∂haarIntegers E := by
  unfold gInt
  simp

theorem gInt_rec (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {χ : AddChar F Circle} (hχ : IsStd χ) (δ : F) :
    gInt E χ δ 0 = hInt E χ δ +
      ((residueCard F : ℂ) ^ 2)⁻¹ * gInt E χ ((unifUnit F : F) ^ 2 * δ) 0 := by
  set c : F := (unifUnit F : F) with hc
  set C : E := algebraMap F E c with hC
  have hC1 : ord C = 1 := h1
  have hC0 : C ≠ 0 := ne_zero_of_ord hC1
  have hcont := cont_chiN h1 hχ (E := E) δ
  have hb : ∀ u : E, ‖(χ (δ * Algebra.norm F u) : ℂ)‖ ≤ 1 := fun u => (Circle.norm_coe _).le
  have i1 : Integrable (fun u : E => (χ (δ * Algebra.norm F u) : ℂ) * uInd u) (haarIntegers E) :=
    (integrable_uInd (K := E)).bdd_mul hcont.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have i2 : Integrable (fun u : E => (χ (δ * Algebra.norm F u) : ℂ) * intInd (C⁻¹ * u)) (haarIntegers E) :=
    (integrable_intInd_mul (inv_ne_zero hC0)).bdd_mul hcont.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  rw [gInt_zero_eq, gInt_zero_eq]
  have e : ∀ u : E, (χ (δ * Algebra.norm F u) : ℂ) * intInd u =
      (χ (δ * Algebra.norm F u) : ℂ) * uInd u + (χ (δ * Algebra.norm F u) : ℂ) * intInd (C⁻¹ * u) := by
    intro u
    rw [intInd_split hC1 u]
    ring
  simp_rw [e]
  rw [integral_add i1 i2]
  congr 1
  have h3 := integral_comp_mul_left (haarIntegers E) (inv_ne_zero hC0)
    (fun x => (χ (δ * Algebra.norm F (C * x)) : ℂ) * intInd x)
  have e3 : ∀ x, (χ (δ * Algebra.norm F (C * (C⁻¹ * x))) : ℂ) * intInd (C⁻¹ * x) =
      (χ (δ * Algebra.norm F x) : ℂ) * intInd (C⁻¹ * x) := by
    intro x
    rw [mul_inv_cancel_left₀ hC0]
  simp_rw [e3] at h3
  rw [h3]
  have e4 : ∀ x : E, (χ (δ * Algebra.norm F (C * x)) : ℂ) * intInd x =
      (χ ((c ^ 2 * δ) * Algebra.norm F x) : ℂ) * intInd x := by
    intro x
    rw [show Algebra.norm F (C * x) = c ^ 2 * Algebra.norm F x by
      rw [(Algebra.norm F).map_mul C x, hC, norm_algebraMap_eq_sq],
      show δ * (c ^ 2 * Algebra.norm F x) = c ^ 2 * δ * Algebra.norm F x by ring]
  simp_rw [e4]
  rw [modulus_inv, modulus_of_ne_zero hC0, hC1, card_E hE.out h1]
  simp

theorem uInd_mul {v : E} (hv : modulus v = 1) (u : E) : uInd (v * u) = uInd u := by
  unfold uInd
  rw [modulus_mul, hv, one_mul]

theorem hInt_unit (χ : AddChar F Circle) (hn : ∀ ε : F, modulus ε = 1 → ∃ t : Eˣ, Algebra.norm F (t : E) = ε)
    (δ : F) {ε : F} (hε : modulus ε = 1) : hInt E χ (δ * ε) = hInt E χ δ := by
  obtain ⟨t, ht⟩ := hn ε hε
  have hv : modulus (t : E) = 1 := by
    rw [← modulus_norm (K := F), ht, hε]
  have h3 := integral_comp_mul_left (haarIntegers E) t.ne_zero
    (fun x => (χ (δ * Algebra.norm F x) : ℂ) * uInd x)
  unfold hInt
  simp only [map_mul, ht, uInd_mul hv, hv] at h3
  have e : ∀ x : E, (χ (δ * ε * Algebra.norm F x) : ℂ) * uInd x =
      (χ (δ * (ε * Algebra.norm F x)) : ℂ) * uInd x := fun x => by rw [mul_assoc]
  simp_rw [e]
  rw [h3]
  simp

theorem hInt_avg (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {χ : AddChar F Circle} (hχ : IsStd χ) (hχE : IsStd (chE E χ))
    (hn : ∀ ε : F, modulus ε = 1 → ∃ t : Eˣ, Algebra.norm F (t : E) = ε) {δ : F} (hδ : δ ≠ 0) :
    hInt E χ δ * (1 - (residueCard F : ℂ)⁻¹) = (1 - (residueCard E : ℂ)⁻¹) *
      (intInd δ - (residueCard F : ℂ)⁻¹ * intInd ((unifUnit F : F) * δ)) := by
  set I : F → E → ℂ := fun ε u => (χ (δ * ε * Algebra.norm F u) : ℂ) * (uInd ε * uInd u) with hI
  have hint : Integrable (Function.uncurry I) ((haarIntegers F).prod (haarIntegers E)) := by
    have hp := (integrable_uInd (K := F)).mul_prod (integrable_uInd (K := E))
    have hc : Continuous fun z : F × E => (χ (δ * z.1 * Algebra.norm F z.2) : ℂ) :=
      cont_circ (hχ.1.comp ((continuous_const.mul continuous_fst).mul ((continuous_norm' h1).comp continuous_snd)))
    exact hp.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => (Circle.norm_coe _).le)
  have hs := integral_integral_swap (μ := haarIntegers F) (ν := haarIntegers E) (f := I) hint
  have l : ∀ ε : F, ∫ u, I ε u ∂haarIntegers E = uInd ε * hInt E χ δ := by
    intro ε
    by_cases hε : modulus ε = 1
    · rw [← hInt_unit χ hn δ hε]
      unfold hInt
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [hI]
      ring
    · have : uInd ε = 0 := by simp [uInd, hε]
      simp [hI, this]
  have r : ∀ u : E, ∫ ε, I ε u ∂haarIntegers F = uInd u *
      (intInd δ - (residueCard F : ℂ)⁻¹ * intInd ((unifUnit F : F) * δ)) := by
    intro u
    by_cases hu : modulus u = 1
    · have hu0 : u ≠ 0 := by
        rintro rfl
        simp at hu
      have hN : Algebra.norm F u ≠ 0 := Algebra.norm_ne_zero_iff.2 hu0
      have hNm : modulus (Algebra.norm F u) = 1 := by rw [modulus_norm, hu]
      have hav := uAvg hχ (δ * Algebra.norm F u)
      have key : ∀ a : F, intInd (a * Algebra.norm F u) = intInd a := by
        intro a
        by_cases ha : a ∈ 𝒪[F]
        · rw [intInd_of_mem ha, intInd_of_mem (modulus_le_one_iff.1 (by
            rw [modulus_mul, hNm, mul_one]; exact modulus_le_one_iff.2 ha))]
        · rw [intInd_of_not_mem ha, intInd_of_not_mem (fun h => ha (modulus_le_one_iff.1 (by
            have := modulus_le_one_iff.2 h
            rwa [modulus_mul, hNm, mul_one] at this)))]
      rw [key, ← mul_assoc, key] at hav
      rw [← hav, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ε => ?_)
      simp only [hI]
      rw [show δ * ε * Algebra.norm F u = δ * Algebra.norm F u * ε by ring]
      ring
    · have : uInd u = 0 := by simp [uInd, hu]
      simp [hI, this]
  simp_rw [l, r] at hs
  rw [integral_mul_const, integral_mul_const, integral_uInd hχ, integral_uInd hχE] at hs
  rw [mul_comm]
  exact hs

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [hE : Fact (Module.finrank F E = 2)]

theorem q_ne : (residueCard F : ℂ) ≠ 0 := by
  exact_mod_cast (residueCard_ne_zero (K := F))

theorem one_sub_ne : 1 - (residueCard F : ℂ)⁻¹ ≠ 0 := by
  intro h
  have h2 : (residueCard F : ℂ) = 1 := by
    have := q_ne (F := F)
    field_simp at h
    linear_combination h
  have h3 : residueCard F = 1 := by exact_mod_cast h2
  have := one_lt_residueCard (K := F)
  omega

theorem hInt_neg_one (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {χ : AddChar F Circle} (hχ : IsStd χ) (hχE : IsStd (chE E χ))
    (hn : ∀ ε : F, modulus ε = 1 → ∃ t : Eˣ, Algebra.norm F (t : E) = ε) {δ : F} (hδ : δ ≠ 0) (ho : ord δ = -1) :
    hInt E χ δ = -((1 + (residueCard F : ℂ)⁻¹) * (residueCard F : ℂ)⁻¹) := by
  have hav := hInt_avg h1 hχ hχE hn hδ
  have hcδ : (unifUnit F : F) * δ ≠ 0 := mul_ne_zero (unifUnit F).ne_zero hδ
  rw [intInd_of_not_mem (fun h => by have := (mem_int_iff_ord hδ).1 h; omega),
    intInd_of_mem ((mem_int_iff_ord hcδ).2 (by rw [ord_mul (unifUnit F).ne_zero hδ, ord_unif, ho]; omega)),
    card_E hE.out h1] at hav
  have hq := q_ne (F := F)
  refine mul_right_cancel₀ (one_sub_ne (F := F)) (hav.trans ?_)
  push_cast
  field_simp
  ring

theorem hInt_low (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {χ : AddChar F Circle} (hχ : IsStd χ) (hχE : IsStd (chE E χ))
    (hn : ∀ ε : F, modulus ε = 1 → ∃ t : Eˣ, Algebra.norm F (t : E) = ε) {δ : F} (hδ : δ ≠ 0) (ho : ord δ ≤ -2) :
    hInt E χ δ = 0 := by
  have hav := hInt_avg h1 hχ hχE hn hδ
  have hcδ : (unifUnit F : F) * δ ≠ 0 := mul_ne_zero (unifUnit F).ne_zero hδ
  rw [intInd_of_not_mem (fun h => by have := (mem_int_iff_ord hδ).1 h; omega),
    intInd_of_not_mem (fun h => by
      have := (mem_int_iff_ord hcδ).1 h
      rw [ord_mul (unifUnit F).ne_zero hδ, ord_unif] at this
      omega)] at hav
  refine mul_right_cancel₀ (one_sub_ne (F := F)) (hav.trans ?_)
  simp

theorem nsg_sq {c : F} (hc : c ≠ 0) (δ : F) : nsg E (c ^ 2 * δ) = nsg E δ := by
  have hC : algebraMap F E c ≠ 0 := by simpa using hc
  have hC' : algebraMap F E c⁻¹ ≠ 0 := by simpa using hc
  have : (∃ t : Eˣ, Algebra.norm F (t : E) = c ^ 2 * δ) ↔ ∃ t : Eˣ, Algebra.norm F (t : E) = δ := by
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t * Units.mk0 _ hC', ?_⟩
      rw [Units.val_mul, Units.val_mk0, (Algebra.norm F).map_mul, ht, norm_algebraMap_eq_sq]
      field_simp
    · rintro ⟨t, ht⟩
      refine ⟨t * Units.mk0 _ hC, ?_⟩
      rw [Units.val_mul, Units.val_mk0, (Algebra.norm F).map_mul, ht, norm_algebraMap_eq_sq]
      ring
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = δ
  · rw [show nsg E δ = 1 from if_pos h, show nsg E (c ^ 2 * δ) = 1 from if_pos (this.2 h)]
  · rw [show nsg E δ = -1 from if_neg h, show nsg E (c ^ 2 * δ) = -1 from if_neg (fun h' => h (this.1 h'))]

theorem nsg_odd (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {δ : F} (ho : ord δ = -1) : nsg E δ = -1 := by
  unfold nsg
  rw [if_neg]
  rintro ⟨t, ht⟩
  have := ord_normE hE.out h1 (t : E)
  rw [ht, ho] at this
  omega

theorem modC {δ : F} (hδ : δ ≠ 0) : (((modulus δ : ℝ)⁻¹ : ℝ) : ℂ) = (residueCard F : ℂ) ^ (ord δ) := by
  rw [modulus_of_ne_zero hδ]
  push_cast
  rw [zpow_neg, inv_inv]

theorem gInt_val (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {χ : AddChar F Circle} (hχ : IsStd χ) (hχE : IsStd (chE E χ))
    (hn : ∀ ε : F, modulus ε = 1 → ∃ t : Eˣ, Algebra.norm F (t : E) = ε) (m : ℕ) :
    ∀ δ : F, δ ≠ 0 → ord δ = -(m : ℤ) - 1 →
      gInt E χ δ 0 = nsg E δ * (((modulus δ : ℝ)⁻¹ : ℝ) : ℂ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro δ hδ ho
  have hc0 : (unifUnit F : F) ≠ 0 := (unifUnit F).ne_zero
  have hδ' : (unifUnit F : F) ^ 2 * δ ≠ 0 := mul_ne_zero (pow_ne_zero _ hc0) hδ
  have ho' : ord ((unifUnit F : F) ^ 2 * δ) = ord δ + 2 := by
    rw [ord_mul (pow_ne_zero _ hc0) hδ, ord_pow hc0, ord_unif]
    push_cast
    ring
  have hq := q_ne (F := F)
  rw [gInt_rec h1 hχ δ, modC hδ]
  match m, ih, ho with
  | 0, _, ho =>
    have ho1 : ord δ = -1 := by simpa using ho
    rw [hInt_neg_one h1 hχ hχE hn hδ ho1, gInt_of_mem hχ hχE ((mem_int_iff_ord hδ').2 (by omega)) 0,
      intInd_of_mem (zero_mem _), nsg_odd h1 ho1, ho1, zpow_neg_one]
    field_simp
    ring
  | 1, _, ho =>
    have ho1 : ord δ = -2 := by
      rw [ho]
      norm_num
    have hns : nsg E δ = 1 := by
      rw [← nsg_sq hc0 δ]
      unfold nsg
      rw [if_pos (hn _ ((modulus_eq_one_iff hδ').2 (by omega)))]
    rw [hInt_low h1 hχ hχE hn hδ ho1.le, gInt_of_mem hχ hχE ((mem_int_iff_ord hδ').2 (by omega)) 0,
      intInd_of_mem (zero_mem _), hns, ho1]
    simp [zpow_neg]
  | (k + 2), ih, ho =>
    have hlow : ord δ ≤ -2 := by
      rw [ho]
      push_cast
      omega
    rw [hInt_low h1 hχ hχE hn hδ hlow, ih k (by omega) _ hδ' (by rw [ho', ho]; push_cast; ring),
      nsg_sq hc0 δ, modC hδ', ho', zpow_add₀ hq]
    field_simp
    norm_cast
    rw [zero_add]

end

theorem gauss_main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ (χ : AddChar F Circle) (η : Fˣ →* ℂˣ), Ad3.IsStd χ → Ad3.IsStd (Ad3.K.GL2LocalData.chE E χ) → ((∀ a, ((η a : ℂˣ) : ℂ) = Ad3.K.GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ Ad3.K.GL2LocalData.nsg E (-1 : F) = 1) → ∀ (δ : F) (y : E), (δ ∈ 𝒪[F] → ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂selfDualMeasure (Ad3.K.GL2LocalData.chE E χ) = intInd y) ∧ (δ ∉ 𝒪[F] → ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂selfDualMeasure (Ad3.K.GL2LocalData.chE E χ) = Ad3.K.GL2LocalData.nsg E δ * (((modulus δ : ℝ)⁻¹ : ℝ) : ℂ) * (χ (-(Algebra.norm F y) / δ) : ℂ) * intInd (y * algebraMap F E δ⁻¹)) := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hd _ h1 χ η hχ hχE hη δ y
  obtain ⟨hη, hun, -, -⟩ := hη
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hd
  haveI : Fact (Module.finrank F E = 2) := ⟨hd⟩
  haveI : Algebra.IsSeparable F E := inferInstance
  have hn : ∀ ε : F, modulus ε = 1 → ∃ t : Eˣ, Algebra.norm F (t : E) = ε := by
    intro ε hε
    have hε0 : ε ≠ 0 := by
      rintro rfl
      simp at hε
    have hm : Units.mk0 ε hε0 ∈ unitFiltrationUnits F 0 :=
      mem_unitFiltrationUnits_zero_iff_ord.2 ((modulus_eq_one_iff hε0).1 hε)
    have h2 : η (Units.mk0 ε hε0) = 1 := hun hm
    have h3 := hη (Units.mk0 ε hε0)
    rw [h2, Units.val_mk0] at h3
    by_contra hcon
    unfold nsg at h3
    rw [if_neg hcon] at h3
    norm_num at h3
  rw [selfDual_std hχE]
  refine ⟨fun hδ => gInt_of_mem hχ hχE hδ y, fun hδ => ?_⟩
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hδ (zero_mem _)
  change gInt E χ δ y = _
  by_cases hy : y * algebraMap F E δ⁻¹ ∈ 𝒪[E]
  · have hm : ∃ m : ℕ, ord δ = -(m : ℤ) - 1 := by
      have := (mem_int_iff_ord hδ0).not.1 hδ
      exact ⟨(-ord δ - 1).toNat, by omega⟩
    obtain ⟨m, hm⟩ := hm
    rw [gInt_shift h1 χ hδ0 hy, gInt_val h1 hχ hχE hn m δ hδ0 hm, intInd_of_mem hy]
    ring
  · rw [gInt_eq_zero h1 hχ hχE hδ hy, intInd_of_not_mem hy, mul_zero]

end GlobalTheory.CompanionTheory.NormGauss

import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.UnitA

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem place {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (val : Valuation K Γ)
    (c d mm : K) (hc : val c ≤ 1) (hm : val mm ≤ 1) (hd : val (d - 1) ≤ val mm ^ 2)
    (hcd : val c = 1 ∨ val d = 1) (e : K) (he : e = if val d = 1 then 0 else 1) :
    val (d + c * e) = 1 ∧ val e ≤ val mm ∧ val ((d + c * e)⁻¹ - 1) ≤ val mm ^ 2 := by
  have hm2 : val mm ^ 2 ≤ 1 := pow_le_one' hm 2
  have hd1 : val d ≤ 1 := by
    have : d = (d - 1) + 1 := by ring
    rw [this]
    refine (val.map_add _ _).trans (max_le (hd.trans hm2) (by simp))
  by_cases h : val d = 1
  · simp only [h, if_true] at he
    subst he
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at h
    refine ⟨by simpa using h, by simp, ?_⟩
    have : (d + c * 0)⁻¹ - 1 = (-(d - 1)) * d⁻¹ := by
      rw [mul_zero, add_zero, neg_sub, sub_mul, mul_inv_cancel₀ hd0, one_mul]
    rw [this, map_mul, map_inv₀, Valuation.map_neg, h]
    simpa using hd
  · simp only [h, if_false] at he
    subst he
    have hlt : val d < 1 := lt_of_le_of_ne hd1 h
    have hc1 : val c = 1 := hcd.resolve_right h
    have hv1 : val (d - 1) = 1 := by
      rw [Valuation.map_sub_eq_of_lt_right val (by simpa using hlt)]
      simp
    have hmm : 1 ≤ val mm ^ 2 := hv1 ▸ hd
    have hm1 : val mm ^ 2 = 1 := le_antisymm hm2 hmm
    have hmv : val mm = 1 := by
      refine le_antisymm hm ?_
      by_contra hlt'
      have : val mm < 1 := not_le.mp hlt'
      have := pow_lt_one₀ zero_le' this (two_ne_zero)
      exact absurd hm1 this.ne
    have hu : val (d + c * 1) = 1 := by
      rw [mul_one, Valuation.map_add_eq_of_lt_right val (by rwa [hc1]), hc1]
    refine ⟨hu, by simp [hmv], ?_⟩
    rw [hm1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (by simp))
    rw [map_inv₀, hu]
    simp

theorem UpperTheory.ConvolutionTheory.R2.C.lvEps :
    ∀ (F : Type) [Field F] [NumberField F] (m : F), m ≠ 0 → Dv 1 (rt m) → ∀ c d : A F, c.1 = 0 → d.1 = 1 → Dv 1 c → Dv (m ^ 2) (d - 1) →
    (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (c.2 v) = 1 ∨ Valued.v (d.2 v) = 1) →
    ∃ (u : (A F)ˣ) (ε x y : A F), Dv 1 (u : A F) ∧ Dv 1 ((u⁻¹ : (A F)ˣ) : A F) ∧ (ε.1 = 0 ∧ Dv m ε) ∧ (x.1 = 0 ∧ Dv m x) ∧ (y.1 = 0 ∧ Dv m y) ∧
      d + c * ε = u ∧ ((u⁻¹ : (A F)ˣ) : A F) = 1 + x * y := by
  intro F _ _ m hm0 hm c d hc1 hd1 hc hd hcd
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((rt m).2 v) = v.valuation F m :=
    fun v => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v m
  have hminv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((rt m⁻¹).2 v) = (v.valuation F m)⁻¹ :=
    fun v => (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v m⁻¹).trans (map_inv₀ _ _)
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (1 : F) = 1 := fun v => map_one _
  let e : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F :=
    fun v => if Valued.v (d.2 v) = 1 then 0 else 1
  have he_int : ∀ v : HeightOneSpectrum (𝓞 F), e v ∈ v.adicCompletionIntegers F := by
    intro v
    by_cases h : Valued.v (d.2 v) = 1
    · simp only [e, h, if_true]
      exact zero_mem _
    · simp only [e, h, if_false]
      exact one_mem _
  let ef : FiniteAdeleRing (𝓞 F) F := ⟨e, Filter.Eventually.of_forall he_int⟩
  let ε : A F := ((0 : InfiniteAdeleRing F), ef)
  have key : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (d.2 v + c.2 v * e v) = 1 ∧ Valued.v (e v) ≤ Valued.v ((rt m).2 v) ∧
      Valued.v ((d.2 v + c.2 v * e v)⁻¹ - 1) ≤ Valued.v ((rt m).2 v) ^ 2 := by
    intro v
    refine place Valued.v (c.2 v) (d.2 v) ((rt m).2 v) ?_ ?_ ?_ (hcd v) (e v) rfl
    · have := hc v
      rwa [hone] at this
    · have := hm v
      rwa [hone] at this
    · have := hd v
      rw [map_pow, ← hmv] at this
      exact this
  have hinf : (d + c * ε).1 = 1 := by
    show d.1 + c.1 * ε.1 = 1
    rw [hd1, hc1, zero_mul, add_zero]
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), (d + c * ε).2 v = d.2 v + c.2 v * e v := fun v => rfl
  have hU : IsUnit (d + c * ε) := by
    refine (UpperTheory.ConvolutionTheory.R2.C.unitA F _).2 ⟨fun w => ?_, fun v => ?_, Filter.Eventually.of_forall fun v => ?_⟩
    · rw [hinf]
      exact one_ne_zero
    · intro h0
      have := (key v).1
      rw [← hfin, h0, map_zero] at this
      exact zero_ne_one this
    · rw [hfin]
      exact (key v).1
  obtain ⟨u, hu⟩ := hU
  have huv : ∀ v : HeightOneSpectrum (𝓞 F), (u : A F).2 v = d.2 v + c.2 v * e v := by
    intro v
    rw [hu]
    rfl
  have hui : ∀ v : HeightOneSpectrum (𝓞 F), ((u⁻¹ : (A F)ˣ) : A F).2 v = ((u : A F).2 v)⁻¹ := by
    intro v
    have h1 : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := u.mul_inv
    have h2 : (u : A F).2 v * ((u⁻¹ : (A F)ˣ) : A F).2 v = 1 := congrArg (fun z : A F => z.2 v) h1
    exact (inv_eq_of_mul_eq_one_right h2).symm
  have hu1 : (u : A F).1 = 1 := by rw [hu, hinf]
  have hui1 : ((u⁻¹ : (A F)ˣ) : A F).1 = 1 := by
    have h1 : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := u.mul_inv
    have h2 : (u : A F).1 * ((u⁻¹ : (A F)ˣ) : A F).1 = 1 := congrArg Prod.fst h1
    rwa [hu1, one_mul] at h2
  have hpq : (rt m).2 * (rt m⁻¹).2 = (1 : FiniteAdeleRing (𝓞 F) F) := by
    have h1 : rt m * rt m⁻¹ = (1 : A F) := by
      rw [← map_mul, mul_inv_cancel₀ hm0, map_one]
    exact congrArg Prod.snd h1
  refine ⟨u, ε, ((0 : InfiniteAdeleRing F), (rt m).2),
    ((0 : InfiniteAdeleRing F), (((u⁻¹ : (A F)ˣ) : A F) - 1).2 * (rt m⁻¹).2), ?_, ?_, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, hu.symm, ?_⟩
  · intro v
    rw [huv, (key v).1, hone]
  · intro v
    rw [hui, map_inv₀, huv, (key v).1, hone, inv_one]
  · intro v
    rw [← hmv]
    exact (key v).2.1
  · intro v
    exact (hmv v).le
  · intro v
    have hne : v.valuation F m ≠ 0 := (Valuation.ne_zero_iff _).2 hm0
    have h1 : Valued.v ((((u⁻¹ : (A F)ˣ) : A F) - 1).2 v) ≤ v.valuation F m ^ 2 := by
      have h2 : (((u⁻¹ : (A F)ˣ) : A F) - 1).2 v = (d.2 v + c.2 v * e v)⁻¹ - 1 := by
        rw [← huv, ← hui]
        rfl
      rw [h2, ← hmv]
      exact (key v).2.2
    have h3 : ((((0 : InfiniteAdeleRing F), (((u⁻¹ : (A F)ˣ) : A F) - 1).2 * (rt m⁻¹).2) : A F)).2 v =
        (((u⁻¹ : (A F)ˣ) : A F) - 1).2 v * (rt m⁻¹).2 v := rfl
    rw [h3, map_mul, hminv]
    calc _ ≤ v.valuation F m ^ 2 * (v.valuation F m)⁻¹ := mul_le_mul_left h1 _
      _ = v.valuation F m := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  · refine Prod.ext ?_ ?_
    · show ((u⁻¹ : (A F)ˣ) : A F).1 = 1 + 0 * _
      rw [hui1, zero_mul, add_zero]
    · show ((u⁻¹ : (A F)ˣ) : A F).2 = 1 + (rt m).2 * ((((u⁻¹ : (A F)ˣ) : A F).2 - 1) * (rt m⁻¹).2)
      linear_combination (-(((u⁻¹ : (A F)ˣ) : A F).2 - 1)) * hpq

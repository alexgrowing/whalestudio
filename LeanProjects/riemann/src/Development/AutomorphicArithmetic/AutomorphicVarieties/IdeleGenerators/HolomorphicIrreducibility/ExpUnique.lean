import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

private def ee {V : Type} [Fintype V] (μ x : V → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ))

private theorem ee_add {V : Type} [Fintype V] (μ x y : V → ℝ) : ee μ (x + y) = ee μ x * ee μ y := by
  simp only [ee, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, Complex.exp_add]

private theorem ee_add' {V : Type} [Fintype V] (μ ν x : V → ℝ) : ee (μ + ν) x = ee μ x * ee ν x := by
  simp only [ee, Pi.add_apply, Complex.ofReal_add, mul_add, add_mul, Finset.sum_add_distrib, Complex.exp_add]

private theorem ee_zero {V : Type} [Fintype V] (μ : V → ℝ) : ee μ 0 = 1 := by simp [ee]

private theorem ee_zero' {V : Type} [Fintype V] (x : V → ℝ) : ee 0 x = 1 := by simp [ee]

private theorem norm_ee {V : Type} [Fintype V] (μ x : V → ℝ) : ‖ee μ x‖ = 1 := by
  have : (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ)) = ((2 * Real.pi * ∑ v, μ v * x v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ee, this, Complex.norm_exp_ofReal_mul_I]

private theorem exists_ee {V : Type} [Fintype V] (μ : V → ℝ) (h : μ ≠ 0) : ∃ g, ee μ g = -1 := by
  classical
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  have hv' : (μ v : ℂ) ≠ 0 := by exact_mod_cast hv
  refine ⟨Pi.single v (1 / (2 * μ v)), ?_⟩
  have : ∑ w, (μ w : ℂ) * ((Pi.single v (1 / (2 * μ v)) : V → ℝ) w : ℂ) = 1 / 2 := by
    rw [Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]; push_cast; field_simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  rw [ee, this, ← Complex.exp_pi_mul_I]
  congr 1; ring

private theorem hs_congr {ι : Type} {f g : ι → ℂ} {d : ℂ} (h : HasSum f d) (e : ∀ i, g i = f i) : HasSum g d :=
  (funext e : g = f) ▸ h

private theorem kill {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * ee (μ i) x) d) (S : Finset ι) :
    ∃ C : ι → ℂ, (∀ i, ‖C i‖ ≤ ‖B i‖) ∧ (∀ i ∈ S, C i = 0) ∧ ∀ x, HasSum (fun i => C i * ee (μ i) x) d := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨B, fun _ => le_rfl, by simp, h⟩
  | insert j S _ ih =>
    obtain ⟨C, h1, h2, h3⟩ := ih
    by_cases hj : B j = 0
    · refine ⟨C, h1, fun i hi => ?_, h3⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simpa [hj] using h1 i
      · exact h2 i hi
    obtain ⟨g, hg⟩ := exists_ee (μ j) (hμ j hj)
    refine ⟨fun i => C i * ((1 + ee (μ i) g) / 2), fun i => ?_, fun i hi => ?_, fun x => ?_⟩
    · have : ‖(1 + ee (μ i) g) / 2‖ ≤ 1 := by
        have := norm_add_le 1 (ee (μ i) g)
        rw [norm_ee, norm_one] at this
        rw [norm_div, Complex.norm_two]; linarith
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) this).trans (h1 i)
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · simp [hg]
      · simp [h2 i hi]
    · have := ((h3 x).add (h3 (x + g))).div_const 2
      rw [show (d + d) / 2 = d by ring] at this
      refine hs_congr this fun i => ?_
      rw [ee_add]; ring

private theorem const_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * ee (μ i) x) d) : d = 0 := by
  have hs : Summable fun i => ‖B i‖ := by
    have := (h 0).summable
    simp only [ee_zero, mul_one] at this
    exact this.norm
  have ht := tendsto_tsum_compl_atTop_zero (fun i => ‖B i‖)
  have : ‖d‖ ≤ 0 := by
    refine ge_of_tendsto' ht fun S => ?_
    obtain ⟨C, h1, h2, h3⟩ := kill μ B d hμ h S
    have h4 := h3 0
    simp only [ee_zero, mul_one] at h4
    have h5 : HasSum (fun i : {x // x ∉ S} => C i) d := by
      refine (hasSum_subtype_iff_of_support_subset (s := {x | x ∉ S}) ?_).2 h4
      intro i hi hS
      exact hi (h2 i hS)
    exact h5.norm_le_of_bounded (hs.subtype _).hasSum fun i => h1 i
  simpa using this

private theorem coef_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (hμ : Function.Injective μ)
    (h : ∀ x, HasSum (fun i => B i * ee (μ i) x) 0) (j : ι) : B j = 0 := by
  classical
  have := const_zero (fun i => μ i - μ j) (fun i => if i = j then 0 else B i) (-B j) (fun i hi => ?_) fun x => ?_
  · simpa using this
  · have : i ≠ j := by rintro rfl; simp at hi
    exact sub_ne_zero.2 (hμ.ne this)
  · have := ((h x).mul_right (ee (-μ j) x)).sub (hasSum_ite_eq j (B j))
    rw [zero_mul, zero_sub] at this
    refine hs_congr this fun i => ?_
    rw [mul_assoc, ← ee_add', ← sub_eq_add_neg]
    by_cases hi : i = j
    · subst hi; simp [ee_zero']
    · simp [hi]

variable {F : Type} [Field F] [NumberField F]

private theorem genD_unique {y : Af F} {𝔪 𝔫 : Ideal (𝓞 F)} (h : GenD y 𝔪) (h' : GenD y 𝔫) : 𝔪 = 𝔫 := by
  have hc : ∀ w : HeightOneSpectrum (𝓞 F), ordI w 𝔪 = ordI w 𝔫 := fun w => by
    have := (h.2 w).symm.trans (h'.2 w)
    rw [WithZero.exp_inj] at this
    omega
  rw [← Ideal.finprod_heightOneSpectrum_factorization h.1, ← Ideal.finprod_heightOneSpectrum_factorization h'.1]
  refine finprod_congr fun w => ?_
  exact congrArg (fun n => w.asIdeal ^ n) (hc w)

private theorem coefAt_eq {y : Af F} {𝔪 : Ideal (𝓞 F)} (h : GenD y 𝔪) (a : Ideal (𝓞 F) → ℂ) : coefAt a y = a 𝔪 := by
  have h' : ∃ 𝔪, GenD y 𝔪 := ⟨𝔪, h⟩
  rw [coefAt, dif_pos h', genD_unique h'.choose_spec h]

private theorem ordI_fin {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ordI w I = 0 := by
  have := Associates.finite_factors (R := 𝓞 F) hI
  filter_upwards [this] with w hw
  exact_mod_cast hw

private theorem exists_genD {𝔪 : Ideal (𝓞 F)} (h : 𝔪 ≠ ⊥) : ∃ y : (Af F)ˣ, GenD (y : Af F) 𝔪 := by
  choose t ht using fun w : HeightOneSpectrum (𝓞 F) => w.valuedAdicCompletion_surjective F
    (WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) - (ordI w 𝔪 : ℤ)))
  have hf : ∀ᶠ w in Filter.cofinite, Valued.v (t w) = 1 := by
    filter_upwards [ordI_fin h, ordI_fin (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot] with w h1 h2
    rw [ht, h1, h2]; simp
  let a : FiniteAdeleRing (𝓞 F) F := ⟨t, by
    filter_upwards [hf] with w hw
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hw.le⟩
  have hu : IsUnit a := FiniteAdeleRing.isUnit_iff.2 ⟨fun w hw => by
    have := ht w
    rw [show t w = 0 from hw, map_zero] at this
    exact WithZero.exp_ne_zero this.symm, hf⟩
  exact ⟨hu.unit, h, fun w => ht w⟩

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.expUnique :
    UpperTheory.V.Sd.ExpUnique := by
  intro F _ _ _ φ k c₀ c₀' a a' h h'
  have key : ∀ (yf : (Af F)ˣ) (x : InfinitePlace F → ℝ),
      HasSum (fun ξ : {ξ : F // ∀ v, 0 < reAt v ξ} =>
        ((coefAt a (algebraMap F (Af F) ξ.1 * (yf : Af F)) - coefAt a' (algebraMap F (Af F) ξ.1 * (yf : Af F))) *
          Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * Complex.I)) * ee (fun v => reAt v ξ.1) x)
        (c₀' yf - c₀ yf) := by
    intro yf x
    have := (h x 1 (by simp) yf).sub (h' x 1 (by simp) yf)
    rw [sub_sub_sub_cancel_left] at this
    refine hs_congr this fun ξ => ?_
    rw [← sub_mul, mul_assoc, ee, ← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 3
    refine Finset.sum_congr rfl fun v _ => ?_
    simp; ring
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hc : ∀ yf, c₀' yf - c₀ yf = 0 := fun yf =>
    const_zero _ _ _ (fun ξ _ h0 => (ξ.2 v₀).ne' (congrFun h0 v₀)) (key yf)
  refine ⟨funext fun yf => (sub_eq_zero.1 (hc yf)).symm, fun 𝔪 hm => ?_⟩
  obtain ⟨y, hy⟩ := exists_genD hm
  have hinj : Function.Injective fun (ξ : {ξ : F // ∀ v, 0 < reAt v ξ}) (v : InfinitePlace F) => reAt v ξ.1 := by
    intro ξ η he
    have h1 : reAt v₀ ξ.1 = reAt v₀ η.1 := congrFun he v₀
    have hr := IsTotallyReal.isReal v₀
    refine Subtype.ext (v₀.embedding.injective ?_)
    rw [← InfinitePlace.embedding_of_isReal_apply hr, ← InfinitePlace.embedding_of_isReal_apply hr]
    simp only [reAt, ← InfinitePlace.embedding_of_isReal_apply hr, Complex.ofReal_re] at h1
    rw [h1]
  have := coef_zero _ _ hinj (fun x => hc y ▸ key y x) ⟨1, fun v => by simp [reAt]⟩
  simp only [map_one, one_mul, mul_eq_zero, Complex.exp_ne_zero, or_false] at this
  rw [coefAt_eq hy, coefAt_eq hy] at this
  exact sub_eq_zero.1 this

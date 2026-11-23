import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.UnRep.StdInhab

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem bar_rt (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.rt = -H.rt := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
  · exfalso
    have e' : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, e]
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have c := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [e'] at c
    have r : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
      simpa using this
    obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 c.symm
    rw [hx] at r
    have r' : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast r
    have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg x]
  · exact e

theorem bar_w (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.w0 = 1 - H.w0 := by
  have h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h4 : (2 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  rw [h2, bar_rt]
  linear_combination H.two_weight_eq_one_add_root

theorem w_norm (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ m : ℕ, 2 ≤ m ∧ H.w0 * H.bar H.w0 = (m : 𝓞 E) := by
  obtain ⟨m, hm⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  refine ⟨m, by have := H.d_mod; omega, ?_⟩
  have hm' : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hm
  rw [bar_w]
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'

theorem w_not_unit (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ¬ IsUnit H.w0 := by
  intro hu
  obtain ⟨m, hm, e⟩ := w_norm H
  have h1 : IsUnit (m : 𝓞 E) := e ▸ hu.mul (hu.map H.bar)
  have h2 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 E) (m : ℤ))) := by
    apply IsUnit.map
    simpa using h1
  rw [Algebra.norm_algebraMap] at h2
  have h3 : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff h3, Int.isUnit_iff] at h2
  omega

theorem w_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.w0 ≠ 0 := by
  obtain ⟨m, hm, e⟩ := w_norm H
  intro h
  rw [h, zero_mul] at e
  have : m = 0 := by exact_mod_cast e.symm
  omega

theorem moved_iff (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (P : Ideal (𝓞 E)) :
    Moved (IsCMField.complexConj E) P ↔ P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P := by
  constructor
  · rintro ⟨a, ha, b, hb, hbP⟩ e
    apply hbP
    have : b = H.bar a := by
      apply Subtype.ext
      show (b : E) = ((H.bar a : 𝓞 E) : E)
      rw [hb, H.bar_eq]
    rw [this, ← e]
    exact Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) ha
  · intro hne
    by_contra hm
    have key : ∀ a ∈ P, H.bar a ∈ P := by
      intro a ha
      by_contra hb
      exact hm ⟨a, ha, H.bar a, H.bar_eq a, hb⟩
    apply hne
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact key a ha
    · intro a ha
      rw [← bar_bar H a]
      exact Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (key a ha)

theorem splitOff_w (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : SplitOff (IsCMField.complexConj E) 1 H.w0 := by
  refine ⟨w_ne_zero H, fun P hP hw => ?_⟩
  have h1 : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one P).1 hP.ne_top
  refine ⟨⟨H.w0, hw, H.bar H.w0, H.bar_eq _, fun hb => h1 ?_⟩, by simpa using h1⟩
  have := P.add_mem hw hb
  rwa [bar_w, add_sub_cancel] at this

omit [IsCMField E] in
theorem single_mem (n : ℕ) (i : Fin n) : (Pi.single i (1 : E) : Fin n → E) ∈ stdLat E n := by
  intro j _
  by_cases h : j = i
  · subst h
    exact Submodule.mem_one.2 ⟨1, by simp⟩
  · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩

omit [IsCMField E] in
theorem stdLat_eq_span (n : ℕ) :
    stdLat E n = Submodule.span (𝓞 E) (Set.range fun i : Fin n => (Pi.single i (1 : E) : Fin n → E)) := by
  apply le_antisymm
  · intro x hx
    have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i => Submodule.mem_one.1 (hx i trivial)
    choose r hr using hx'
    have : x = ∑ i, r i • (Pi.single i (1 : E) : Fin n → E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem n i

theorem hermE_one {F : Type} [Field F] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (x y : Fin n → E) :
    hermE c 1 x y = ∑ a, x a * c (y a) := by
  unfold hermE
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.one_apply]

theorem isUnE_one_iff {F : Type} [Field F] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) :
    IsUnE c 1 γ ↔ ∀ i j, ∑ b, c (γ b i) * γ b j = if i = j then 1 else 0 := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [hermE_one, hermE_one] at this
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [mul_comm (c _)]
    rw [this]
    by_cases e : i = j
    · subst e; simp [Pi.single_apply]
    · simp [Pi.single_apply, e, Ne.symm e]
  · intro h x y
    rw [hermE_one, hermE_one]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    calc ∑ a, ∑ i, ∑ j, γ a j * x j * (c (γ a i) * c (y i))
        = ∑ i, ∑ j, (∑ a, c (γ a i) * γ a j) * (x j * c (y i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = _ := by simp [h]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n : ℕ), IsHermForm (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) ∧ Module.finrank (maximalRealSubfield E) E = 2 ∧ (stdLat E n).FG ∧ Submodule.span E (stdLat E n : Set (Fin n → E)) = ⊤ ∧ SplitOff (IsCMField.complexConj E) 1 H.w0 ∧ ¬ IsUnit H.w0 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → (Moved (IsCMField.complexConj E) P ↔ P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P)) ∧ ∀ γ : Matrix (Fin n) (Fin n) E, IsUnE (IsCMField.complexConj E) 1 γ ↔ ∀ i j, ∑ b, (IsCMField.complexConj E) (γ b i) * γ b j = if i = j then 1 else 0 := by
  intro E _ _ _ H n
  refine ⟨⟨IsCMField.complexConj_apply_apply E, IsCMField.complexConj_ne_one E, fun a b => ?_, by simp⟩,
    Algebra.IsQuadraticExtension.finrank_eq_two _ _, ?_, ?_, splitOff_w H, w_not_unit H,
    fun P _ => moved_iff H P, isUnE_one_iff _⟩
  · by_cases e : a = b
    · subst e; simp
    · simp [Matrix.one_apply, e, Ne.symm e]
  · rw [stdLat_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    simpa using single_mem (E := E) n i

end GlobalTheory.UnRep.StdInhab

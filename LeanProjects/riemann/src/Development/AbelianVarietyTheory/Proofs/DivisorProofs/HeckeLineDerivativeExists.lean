import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParaSpan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviLineChar

theorem exists_hasDerivAt_of_mul {g : ℝ → ℂ} (hg : Continuous g) (h0 : g 0 = 1)
    (hm : ∀ s u, g (s + u) = g s * g u) (x : ℝ) : ∃ c, HasDerivAt g c x := by
  set G : ℝ → ℂ := fun y => ∫ u in (0 : ℝ)..y, g u with hGdef
  have hG : ∀ y, HasDerivAt G (g y) y := fun y => (hg.integral_hasStrictDerivAt 0 y).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, G δ ≠ 0 := by
    by_contra h
    push_neg at h
    have h1 : G = fun _ => 0 := funext h
    have h2 := hG 0
    rw [h1] at h2
    have := h2.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at this
    exact one_ne_zero this
  have key : ∀ s, g s = (G (s + δ) - G s) / G δ := by
    intro s
    rw [eq_div_iff hδ]
    have e1 : G (s + δ) - G s = ∫ u in s..s + δ, g u := by
      simp only [hGdef]
      rw [intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
    have e2 : (∫ u in s..s + δ, g u) = ∫ u in (0 : ℝ)..δ, g (u + s) := by
      rw [intervalIntegral.integral_comp_add_right]
      simp [add_comm]
    rw [e1, e2]
    simp only [hGdef]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    rw [add_comm u s, hm]
  refine ⟨(g (x + δ) - g x) / G δ, ?_⟩
  have hd : HasDerivAt (fun s => (G (s + δ) - G s) / G δ) ((g (x + δ) - g x) / G δ) x :=
    (((hG (x + δ)).comp_add_const x δ).sub (hG x)).div_const (G δ)
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => key s)

end GlobalTheory.LeviLineChar

noncomputable section

namespace GlobalTheory.LeviLineChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d d₁ : ℕ}

theorem continuous_levi_scalar (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (hx : H'.x ≠ 0)
    (γ : Multiplicative ℝ →* UA σ W.J) (hγ : Continuous γ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J)
    (t : Multiplicative ℝ →* (AE F E)ˣ) (ht : ∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) :
    Continuous fun s : ℝ => t (Multiplicative.ofAdd s) := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨i, hi⟩ : ∃ i, H'.x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have hu : IsUnit (incV F H'.x i) := (Ne.isUnit hi).map (inclR (F := F) (AF F))
  have hval : ∀ s : Multiplicative ℝ, (t s : AE F E) = (mat (γ s) *ᵥ incV F H'.x) i * hu.unit⁻¹ := by
    intro s
    have h1 := congrFun (ht s).1 i
    rw [Pi.smul_apply, smul_eq_mul] at h1
    rw [h1, mul_assoc, hu.mul_val_inv, mul_one]
  have hc : Continuous fun s : Multiplicative ℝ => (t s : AE F E) := by
    simp_rw [hval]
    have hm : Continuous fun s : Multiplicative ℝ => mat (γ s) := by
      unfold mat
      fun_prop
    exact ((continuous_apply i).comp (hm.matrix_mulVec continuous_const)).mul continuous_const
  have hc' : Continuous fun s : ℝ => (t (Multiplicative.ofAdd s) : AE F E) := hc.comp continuous_ofAdd
  refine Units.continuous_iff.2 ⟨hc', ?_⟩
  have : (fun s : ℝ => ((t (Multiplicative.ofAdd s))⁻¹ : (AE F E)ˣ).1) = fun s => (t (Multiplicative.ofAdd (-s)) : AE F E) := by
    funext s
    rw [← map_inv, ofAdd_neg]
  rw [this]
  exact hc'.comp continuous_neg

end GlobalTheory.LeviLineChar

noncomputable section

namespace GlobalTheory.LeviLineChar

theorem hasDerivAt_levi_char : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d d₁ : ℕ}
    (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), H'.x ≠ 0 →
    ∀ γ ∈ Lines σ W, ∀ γ₁ ∈ Lines σ W₁, ∀ t : Multiplicative ℝ →* (AE F E)ˣ, (∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ z : ℝ,
      ∃ c : ℂ, HasDerivAt (fun s : ℝ => (χ (t (Multiplicative.ofAdd s)) : ℂ) *
        (((absE F E (t (Multiplicative.ofAdd s)) : ℝ) ^ z : ℝ) : ℂ)) c 0 := by
  intro F E _ _ _ _ _ σ d d₁ W W₁ H' hx γ hγ γ₁ _ t ht χ hχ z
  have htc := continuous_levi_scalar W W₁ H' hx γ hγ.1 γ₁ t ht
  have hpos : ∀ s, (absE F E (t (Multiplicative.ofAdd s)) : ℝ) ≠ 0 := by
    intro s
    have := (Group.isUnit (t (Multiplicative.ofAdd s))).map (absE F E)
    exact_mod_cast this.ne_zero
  refine exists_hasDerivAt_of_mul ?_ ?_ ?_ 0
  · refine (continuous_subtype_val.comp (hχ.1.comp htc)).mul (Complex.continuous_ofReal.comp ?_)
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp htc)).rpow_const fun s => Or.inl (hpos s)
  · simp
  · intro s u
    rw [ofAdd_add, map_mul, map_mul, Circle.coe_mul, map_mul, NNReal.coe_mul,
      Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), Complex.ofReal_mul]
    ring

end GlobalTheory.LeviLineChar

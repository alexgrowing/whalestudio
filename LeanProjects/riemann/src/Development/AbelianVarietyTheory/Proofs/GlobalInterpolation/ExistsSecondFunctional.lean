import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.SecondFunctional

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

theorem mem_primeOf_prPbar {σ : E →ₐ[F] E}
    {φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    (hφ : IsSplitting σ v φ) (a : intV E v) :
    a ∈ primeOf (prPbar φ) ↔ Valued.v (prPbar φ a) < 1 := by
  refine ⟨fun h => ?_, fun h => Ideal.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    have hc : Valued.v (prPbar φ c) ≤ 1 := ((hφ.2.2 c).1 c.2).2
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc zero_le' hx

theorem exists_max {ι : Type} (g : ι → WithZero (Multiplicative ℤ)) (t : WithZero (Multiplicative ℤ))
    (ht : t ≠ 0) (hb : ∀ y, t * g y ≤ 1) (y₁ : ι) (h₁ : g y₁ ≠ 0) : ∃ y₀, ∀ y, g y ≤ g y₀ := by
  obtain ⟨n, ⟨y₀, hy₀⟩, hn⟩ := Int.exists_greatest_of_bdd (P := fun n => ∃ y, g y = WithZero.exp n)
    ⟨-WithZero.log t, fun z ⟨y, hy⟩ => by
      have := hb y
      rw [hy, ← WithZero.exp_log ht, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
      omega⟩ ⟨_, y₁, (WithZero.exp_log h₁).symm⟩
  refine ⟨y₀, fun y => ?_⟩
  by_cases hy : g y = 0
  · rw [hy]; exact zero_le'
  · rw [hy₀, ← WithZero.exp_log hy, WithZero.exp_le_exp]
    exact hn _ ⟨y, (WithZero.exp_log hy).symm⟩

theorem hform_add_right {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y z : n → A) : hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
  simp [hform, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) (a : A) : hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_nsmul_left {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) (T : ℕ) : hform σ J (T • x) y = T * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 800000 in

theorem exists_second_functional :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (k : ℕ) (J : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) (L₁ L₂ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)), (∀ y ∈ L₁, ∀ x ∈ L₂, hform (sigR σ (v.adicCompletion F)) J x y ∈ intV E v) → (∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform (sigR σ (v.adicCompletion F)) J x y ∈ intV E v) → ∀ (T : ℕ), T ≠ 0 → (∀ x ∈ L₂, T • x ∈ L₁) → (∃ x ∈ L₂, x ∉ L₁ ∧ ∀ i, prPbar s (x i) = 0) → ∃ f : L₂ →ₗ[intV E v] (intV E v ⧸ primeOf (prPbar s)), Function.Surjective f ∧ (∀ x : L₂, x.1 ∈ L₁ → f x = 0) ∧ ∀ x : L₂, (∀ i, prPbar s (x.1 i) = 0) → f x = 0 := by
  intro F E _ _ _ _ _ σ v s hs k J L₁ L₂ h1 h2 T hT hTL ⟨x, hx2, hx1, hx0⟩
  obtain ⟨H, hH⟩ : ∃ H : (Fin k → E ⊗[F] v.adicCompletion F) → E ⊗[F] v.adicCompletion F,
    ∀ y, H y = hform (sigR σ (v.adicCompletion F)) J x y := ⟨_, fun _ => rfl⟩
  have e2 : ∀ a, prPbar s a = (s a).2 := fun _ => rfl
  have hfst : ∀ y, (s (H y)).1 = 0 := by
    intro y
    have : ∀ i, prP s (sigR σ (v.adicCompletion F) (x i)) = 0 := fun i =>
      (congrArg Prod.fst (hs.2.1 (x i))).trans (hx0 i)
    show prP s (H y) = 0
    simp only [hH, hform, map_sum, map_mul, this, zero_mul, Finset.sum_const_zero]
  have hTK : (T : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hT)
  obtain ⟨y₁, hy₁, hy₁'⟩ : ∃ y ∈ L₂, H y ∉ intV E v := by
    by_contra hc
    push_neg at hc
    exact hx1 ((h2 x).2 fun y hy => hH y ▸ hc y hy)
  have hgt : 1 < Valued.v (prPbar s (H y₁)) := by
    by_contra hc
    exact hy₁' ((hs.2.2 _).2 ⟨by rw [hfst]; exact zero_mem _, not_lt.1 hc⟩)
  obtain ⟨y₀, hy₀⟩ := exists_max (fun y : L₂ => Valued.v (prPbar s (H y))) (Valued.v (T : v.adicCompletion F))
    (by simpa using hTK) (fun y => by
      have h := ((hs.2.2 _).1 ((h2 _).1 (hTL x hx2) y y.2)).2
      rw [hform_nsmul_left, ← e2, map_mul, map_natCast, ← hH] at h
      rw [← map_mul]; exact h) ⟨y₁, hy₁⟩ (ne_of_gt (lt_trans zero_lt_one hgt))
  obtain ⟨c, hc⟩ : ∃ c, c = prPbar s (H y₀) := ⟨_, rfl⟩
  replace hy₀ : ∀ y : L₂, Valued.v (prPbar s (H y)) ≤ Valued.v c := hc ▸ hy₀
  have hc1 : 1 < Valued.v c := lt_of_lt_of_le hgt (hy₀ ⟨y₁, hy₁⟩)
  have hcv : 0 < Valued.v c := lt_trans zero_lt_one hc1
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hcv; exact lt_irrefl _ hcv
  obtain ⟨d, hd⟩ : ∃ d, d = s.symm (0, c⁻¹) := ⟨_, rfl⟩
  have hd2 : ∀ y, prPbar s (H y * d) = prPbar s (H y) / c := fun y => by
    rw [map_mul, e2 d, hd, s.apply_symm_apply, div_eq_mul_inv]
  have hmem : ∀ y : L₂, H y * d ∈ intV E v := fun y => by
    refine (hs.2.2 _).2 ⟨?_, ?_⟩
    · rw [map_mul, Prod.fst_mul, hfst, zero_mul]; exact zero_mem _
    · show Valued.v (prPbar s (H y * d)) ≤ 1
      rw [hd2, map_div₀, div_le_one₀ hcv]
      exact hy₀ y
  let g : L₂ →ₗ[intV E v] intV E v :=
    { toFun := fun y => ⟨H y * d, hmem y⟩
      map_add' := fun y z => Subtype.ext (by
        show H (y.1 + z.1) * d = H y * d + H z * d
        simp only [hH, hform_add_right, add_mul])
      map_smul' := fun a y => Subtype.ext (by
        show H ((a : E ⊗[F] v.adicCompletion F) • y.1) * d = a * (H y * d)
        simp only [hH, hform_smul_right, mul_assoc]) }
  have hg : ∀ y : L₂, prPbar s (g y) = prPbar s (H y) / c := fun y => hd2 y
  have hz : ∀ y : L₂, Valued.v (prPbar s (H y)) ≤ 1 → (primeOf (prPbar s)).mkQ (g y) = 0 := by
    intro y hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_primeOf_prPbar hs, hg, map_div₀,
      div_lt_one₀ hcv]
    exact lt_of_le_of_lt hy hc1
  refine ⟨(primeOf (prPbar s)).mkQ ∘ₗ g, fun b => ?_, fun y hy => hz y ?_, fun y hy => hz y ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine ⟨a • y₀, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_primeOf_prPbar hs, map_smul,
      smul_eq_mul, AddSubgroupClass.coe_sub, Subring.coe_mul, map_sub, map_mul, hg, ← hc, div_self hc0]
    simp
  · rw [hH]; exact ((hs.2.2 _).1 (h1 y hy x hx2)).2
  · have : prPbar s (H y) = 0 := by
      simp only [hH, hform, map_sum, map_mul, hy, mul_zero, Finset.sum_const_zero]
    rw [this]; simp

end GlobalTheory.SecondFunctional

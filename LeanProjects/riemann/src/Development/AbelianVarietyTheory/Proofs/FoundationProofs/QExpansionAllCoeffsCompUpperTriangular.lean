import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNQ

theorem qAll_affine : ∀ (E : Subring ℂ) (N a d : ℕ) (b : ℤ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N f → QAll (· ∈ E) (N * d) fun τ => up f (((a : ℂ) * τ + b) / d) := by
  intro E N a d b f hE hN ha hd hf
  obtain ⟨c, hc, hcE⟩ := hf
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let e : ℕ → ℂ := fun k => Complex.exp (2 * Real.pi * Complex.I * (((k : ℚ) * b / (N * d) : ℚ) : ℂ))
  refine ⟨fun m => if a ∣ m then c (m / a) * e (m / a) else 0, ?_, ?_⟩
  · intro τ
    have hz : 0 < (((a : ℂ) * τ + b) / d).im := by
      have : (((a : ℂ) * τ + b) / d).im = a * τ.im / d := by
        simp [Complex.div_ofReal_im]
      rw [this]; have := τ.im_pos; positivity
    have hτ := hc (UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at hτ
    simp only [UpperHalfPlane.coe_mk_subtype] at hτ
    have hinj : Function.Injective (fun k : ℕ => a * k) := fun x y h => by
      simpa [ha.ne'] using h
    rw [← hinj.hasSum_iff]
    · show HasSum (fun k => _) (f _)
      convert hτ using 1
      funext k
      simp only [Function.comp, dvd_mul_right, if_true, Nat.mul_div_cancel_left k ha, e]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
      ring
      exact congrArg f (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
    · intro m hm
      have : ¬ a ∣ m := by
        rintro ⟨k, rfl⟩; exact hm ⟨k, rfl⟩
      simp [this]
  · intro m
    by_cases h : a ∣ m
    · simp only [h, if_true]
      exact E.mul_mem (hcE _) (hE _)
    · simp only [h, if_false]; exact E.zero_mem

end GlobalTheory.FNQ

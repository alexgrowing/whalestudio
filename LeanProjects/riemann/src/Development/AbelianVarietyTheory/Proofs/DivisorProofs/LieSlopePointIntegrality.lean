import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeightParts.StepFromSlope

theorem latRank_le {K : Type} [Field K] [NumberField K] {m : ℕ} (W : Submodule (𝓞 K) (Fin m → K)) :
    (latRank K W : ℝ) ≤ m := by
  have h := Submodule.finrank_le (Submodule.span K (W : Set (Fin m → K)))
  simp only [Module.finrank_fin_fun] at h
  exact_mod_cast h

theorem log_two_add_le {x a c : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hc : 0 ≤ c) (h : x ≤ a + c) :
    Real.log (2 + x) ≤ Real.log (2 + a) + Real.log (1 + c) := by
  rw [← Real.log_mul (by linarith) (by linarith)]
  exact Real.log_le_log (by linarith) (by nlinarith)

theorem absorb {k C₁ C₀ l : ℝ} (hk : 0 ≤ k) (hC₁ : 0 ≤ C₁) (hC₀ : 0 ≤ C₀) (hl : Real.log 2 ≤ l) :
    k * C₁ * (l + Real.log (1 + C₀)) + C₀ ≤
      (k * C₁ * (1 + Real.log (1 + C₀) / Real.log 2) + C₀ / Real.log 2) * l := by
  have l2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc : 0 ≤ Real.log (1 + C₀) := Real.log_nonneg (by linarith)
  have h1 : Real.log (1 + C₀) ≤ Real.log (1 + C₀) / Real.log 2 * l := by
    rw [div_mul_eq_mul_div, le_div_iff₀ l2]; nlinarith
  have h2 : C₀ ≤ C₀ / Real.log 2 * l := by
    rw [div_mul_eq_mul_div, le_div_iff₀ l2]; nlinarith
  have h3 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hk hC₁)
  nlinarith

end GlobalTheory.HeightParts.StepFromSlope

namespace GlobalTheory.HeightParts

open StepFromSlope in

theorem stepInt_of_lieSlope : LieSlope → PtInt → StepInt := by
  intro hS hP D O hc hf A T H hR
  obtain ⟨C₀, hC₀⟩ := hP D O hc hf A T H hR
  obtain ⟨C₁, hC₁, hL⟩ := hS (D.R.f * O.N)
  have l2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hm : (0 : ℝ) ≤ ((D.R.f * O.N : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨((D.R.f * O.N : ℕ) : ℝ) * C₁ * (1 + Real.log (1 + max C₀ 0) / Real.log 2) + max C₀ 0 / Real.log 2,
    by have : 0 ≤ Real.log (1 + max C₀ 0) := Real.log_nonneg (by linarith [le_max_right C₀ 0])
       positivity, ?_⟩
  intro y hy
  obtain ⟨K, _, _, F, h, hg, hH, hrd, hst⟩ := hC₀ y hy
  have hfalt : H.falt y = omHt O O.met.hm y := by rw [hR.ht.falt y hy]; rfl
  obtain ⟨-, hmu⟩ := hL K F hg.le h hH
  set φ := omHt O O.met.hm y with hφ
  have hC0 : C₀ ≤ max C₀ 0 := le_max_left _ _
  have hC0' : 0 ≤ max C₀ 0 := le_max_right _ _
  have ha : 0 ≤ max φ 0 := le_max_right _ _
  have hl : Real.log 2 ≤ Real.log (2 + max φ 0) := Real.log_le_log (by norm_num) (by linarith)
  have hab := abs_le.mp hrd

  have hν : C₁ * Real.log (2 + max (F.falt h) 0) ≤ C₁ * (Real.log (2 + max φ 0) + Real.log (1 + max C₀ 0)) := by
    refine mul_le_mul_of_nonneg_left (log_two_add_le (le_max_right _ _) ha hC0' ?_) hC₁
    refine max_le ?_ (by linarith)
    simp only [SemiFib.falt]; linarith [le_max_left φ 0]
  have hν0 : 0 ≤ C₁ * Real.log (2 + max (F.falt h) 0) :=
    mul_nonneg hC₁ (Real.log_nonneg (by linarith [le_max_right (F.falt h) 0]))
  have hdeg : ∀ W ≤ F.lieLat, deg h W ≤
      ((D.R.f * O.N : ℕ) : ℝ) * C₁ * (Real.log (2 + max φ 0) + Real.log (1 + max C₀ 0)) := by
    intro W hW
    have h1 := hmu W hW
    have h2 : (latRank K W : ℝ) ≤ ((D.R.f * O.N : ℕ) : ℝ) := hg ▸ latRank_le W
    calc deg h W ≤ latRank K W * (C₁ * Real.log (2 + max (F.falt h) 0)) := h1
      _ ≤ ((D.R.f * O.N : ℕ) : ℝ) * (C₁ * Real.log (2 + max (F.falt h) 0)) :=
          mul_le_mul_of_nonneg_right h2 hν0
      _ ≤ ((D.R.f * O.N : ℕ) : ℝ) * (C₁ * (Real.log (2 + max φ 0) + Real.log (1 + max C₀ 0))) :=
          mul_le_mul_of_nonneg_left hν hm
      _ = _ := by ring
  have key := absorb hm hC₁ hC0' hl
  rw [hfalt]
  refine ⟨?_, fun τ k hk => ?_⟩
  · have := hdeg F.lieLat le_rfl
    linarith
  · obtain ⟨W, hW, -, hWd⟩ := hst τ k hk
    have := hdeg W hW
    have := (abs_le.mp hWd).1
    linarith

end GlobalTheory.HeightParts

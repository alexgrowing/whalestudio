import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRochAsymptotic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosureRR

theorem eventually_le_of_abs_sub_le (k C : ℕ) (T : ℤ) (q : ℚ) (hq : q < T) (h : ℕ → ℕ)
    (hC : ∀ m : ℕ, |(k.factorial : ℤ) * (h m : ℤ) - T * (m : ℤ) ^ k| ≤
      C * ((k : ℤ) * ((m : ℤ) + 1) ^ (k - 1))) :
    ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤ (h l : ℚ) := by
  have hf : (0 : ℚ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hε : (0 : ℚ) < (T : ℚ) - q := sub_pos.2 hq
  obtain ⟨N, hN⟩ := exists_nat_ge ((C : ℚ) * k * 2 ^ (k - 1) / ((T : ℚ) - q))
  refine ⟨N + 1, fun l hl => ?_⟩
  have hm : (1 : ℚ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hNl : (N : ℚ) ≤ l := by exact_mod_cast (show N ≤ l by omega)
  have hB : (C : ℚ) * k * 2 ^ (k - 1) ≤ ((T : ℚ) - q) * l := by
    have := (div_le_iff₀ hε).1 (hN.trans hNl)
    linarith
  have a := hC l
  rw [abs_le] at a
  have a' : (T : ℚ) * (l : ℚ) ^ k - (C : ℚ) * ((k : ℚ) * ((l : ℚ) + 1) ^ (k - 1)) ≤
      (k.factorial : ℚ) * (h l : ℚ) := by
    have := a.1
    have e : ((T * (l : ℤ) ^ k - C * ((k : ℤ) * ((l : ℤ) + 1) ^ (k - 1)) : ℤ) : ℚ) ≤
        (((k.factorial : ℤ) * (h l : ℤ) : ℤ) : ℚ) := Int.cast_le.2 (by linarith)
    push_cast at e
    exact e
  rw [div_le_iff₀ hf]
  rcases k with _ | j
  · simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, zero_mul,
      mul_zero, sub_zero, one_mul] at a' ⊢
    linarith
  · simp only [Nat.add_sub_cancel] at a' hB
    have h2 : ((l : ℚ) + 1) ^ j ≤ 2 ^ j * (l : ℚ) ^ j := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) j
    have hl0 : (0 : ℚ) ≤ (l : ℚ) ^ j := by positivity
    have hCk : (0 : ℚ) ≤ (C : ℚ) * ((j + 1 : ℕ) : ℚ) := by positivity
    have e1 : (C : ℚ) * (((j + 1 : ℕ) : ℚ) * ((l : ℚ) + 1) ^ j) ≤
        (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j := by
      have := mul_le_mul_of_nonneg_left h2 hCk
      nlinarith
    have e2 : (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j ≤ ((T : ℚ) - q) * l * (l : ℚ) ^ j :=
      mul_le_mul_of_nonneg_right hB hl0
    rw [pow_succ] at a' ⊢
    nlinarith

end GlobalTheory.ClosureRR

namespace GlobalTheory.ClosureRR

theorem h0_ge_of_lt_interNumRed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X) (k : ℕ) (q : ℚ),
  IsAmpleLB (toLB A) → letI := algebraΓOfHom p; topologicalKrullDim (closure ({z} : Set X)) = k →
  q < (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤
    (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) : ℚ) := by
  intro X _ _ p hp A z k q hA
  letI := algebraΓOfHom p
  intro hdim hq
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)
  have hi : ∀ r : ℂ, (redι (Closeds.closure ({z} : Set X))).appTop (algebraMap ℂ Γ(X, ⊤) r) =
      algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) r :=
    fun r => rfl
  have hpq : IsProjOver (redι (Closeds.closure ({z} : Set X)) ≫ p) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι (Closeds.closure ({z} : Set X)) ≫ f, inferInstance, by rw [Category.assoc, hs]⟩
  have hstr : strHom ℂ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme =
      redι (Closeds.closure ({z} : Set X)) ≫ p := strHom_eq fun _ => rfl
  have hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme = k :=
    (topologicalKrullDim_red _).trans hdim
  have hNef : IsNef ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) :=
    (IsAmpleLB.isNef (k := ℂ) hA).pull_of_isClosedImmersion _ hi
  obtain ⟨C, hC⟩ := NefRiemannRoch.abs_factorial_mul_sections_sub_top_le ℂ _ (hstr ▸ hpq) k hD.le _ hNef
  have heq : interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin k => toLB A) =
      topSelfIntersection ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) k :=
    interNumOn_const_eq_topSelf hi (isLB_toLB A) k
  have hH : ∀ l : ℕ, lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) =
      lbH0 ℂ (lbPow ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) l) := fun l =>
    lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB (isLB_toLB _) _) (isLB_lbPow (pull_isLB (isLB_toLB A) _) l)
      (by rw [cls_lbPow (pull_isLB (isLB_toLB A) _), cls_pull (isLB_toLB _), cls_pull (isLB_toLB A),
        ← toPic_apply, ← toPic_apply, map_nsmul, map_nsmul])
  rw [heq] at hq
  obtain ⟨l₁, hl₁⟩ := eventually_le_of_abs_sub_le k C _ q hq _ hC
  exact ⟨l₁, fun l hl => by rw [hH l]; exact hl₁ l hl⟩

end GlobalTheory.ClosureRR

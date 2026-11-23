import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionProduct
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionProduct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem isMultiHomog_pow {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (j : ℕ) :
    IsMultiHomog (g ^ j) (j • d) := by
  induction j with
  | zero =>
    have h := SectionBoundedMul.isMultiHomog_monomial (ι := ι) 0 1
    have h1 : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by simpa using h
    rw [pow_zero, zero_smul]
    exact h1
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    exact SectionBoundedMul.isMultiHomog_mul ih hg

end SectionProduct

open SectionBoundedMul SectionProduct in

theorem SectionProduct.proof : SectionProduct.Statement := by
  intro K _ ι _ Ω _ y A B C n j τ s t hdeg hmet hs ht
  have hdk : ∀ k, (τ : ℤ) * C.a k = (n : ℤ) * A.a k + (j : ℤ) * B.a k := fun k => by
    have := congrFun hdeg k
    simpa [smul_eq_mul] using this
  refine ⟨?_, ?_⟩
  ·
    intro c hc
    have hs' := hs c hc
    have ht' := ht c hc
    have heq : s * t ^ j * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k))) *
          (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := by
      have hp : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
          y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k)) * (y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := fun k => by
        have h0 := hc k
        rw [← zpow_natCast (y ⟨k, c k⟩ ^ _) j, ← zpow_mul, ← zpow_add₀ h0, hdk k]
        congr 1
        push_cast
        ring
      simp only [hp, Finset.prod_mul_distrib, Finset.prod_pow]
      ring
    rw [heq]
    exact mul_mem hs' (pow_mem ht' j)
  ·
    intro cc cc' hbs hbt dG dH G H z hG hH hdGH hrep hz
    choose c hc using hz.1
    have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      have hX : IsMultiHomog (X ⟨k, c k⟩ : MRing ι) _ :=
        (by have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
            rwa [← X] at h)
      have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
      have hz0 := hz.2 _ hmem
      simp only [map_X, eval_X] at hz0
      exact hc k hz0
    obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a n hs c hy
    obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y B.a 1 ht c hy
    have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
    have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

    have hdeq : dgs + j • dgt + dH = dG + (N + j • M) := by
      funext k
      have e1 := hdgs k
      have e2 := hdgt k
      have e3 := hdGH k
      have e4 := hdk k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : ((dgs k + j * dgt k + dH k : ℕ) : ℤ) = ((dG k + (N k + j * M k) : ℕ) : ℤ) := by
        push_cast at e1 e2 e3 ⊢
        linear_combination e1 + (j : ℤ) * e2 - e3 - e4
      exact_mod_cast this
    have hF : IsMultiHomog (gs * gt ^ j * H - G * chartMono c (N + j • M)) (dgs + j • dgt + dH) := by
      refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs (isMultiHomog_pow hgt j)) hH) ?_
      rw [hdeq]
      exact isMultiHomog_mul hG (isMultiHomog_chartMono c (N + j • M))
    have hmono : ∀ {R : Type} [CommRing R] (w : (Σ k, ι k) → R),
        ∏ k, w ⟨k, c k⟩ ^ (N + j • M) k = (∏ k, w ⟨k, c k⟩ ^ N k) * (∏ k, w ⟨k, c k⟩ ^ M k) ^ j := by
      intro R _ w
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_add, pow_mul']
    have hF0 : aeval y (gs * gt ^ j * H - G * chartMono c (N + j • M)) = 0 := by
      rw [map_sub, map_mul, map_mul, map_pow, map_mul, hvs, hvt, hrep, aeval_chartMono, aeval_chartMono,
        aeval_chartMono, hmono]
      ring
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
    simp only [map_sub, map_mul, map_pow] at hz0
    rw [sub_eq_zero] at hz0

    set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
    have hmz : ev (chartMono c (N + j • M)) = ev (chartMono c N) * ev (chartMono c M) ^ j := by
      simp only [hev, eval_chartMono]
      exact hmono z
    have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j := by
      refine mul_pos (norm_pos_iff.mpr ?_) (pow_pos (norm_pos_iff.mpr ?_) j) <;>
      · simp only [hev, eval_chartMono]
        exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have key : ‖ev G‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) =
        ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖ := by
      rw [← norm_pow, ← norm_mul, ← hmz, ← norm_mul, ← norm_pow, ← norm_mul, ← norm_mul]
      exact congrArg norm hz0.symm
    have hprod : ‖ev gs‖ * ‖ev gt‖ ^ j ≤
        (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j :=
      mul_le_mul bs (pow_le_pow_left₀ (norm_nonneg _) bt j) (pow_nonneg (norm_nonneg _) j)
        ((norm_nonneg _).trans bs)
    rw [hmet z hz]
    refine le_of_mul_le_mul_right ?_ hpos
    rw [key]
    calc ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖
        ≤ (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j * ‖ev H‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = cc * cc' ^ j * ‖ev H‖ * (A.h z ^ n * B.h z ^ j) *
            (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) := by
          ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

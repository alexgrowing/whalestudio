import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CxDescent

noncomputable def imForm (n : ℕ) (ρ : ℝ) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v u => (∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (u j)).im)
    (by intro v v' u; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by intro c v u; simp [Finset.mul_sum, Complex.mul_im, Complex.mul_re]; exact Finset.sum_congr rfl (fun i _ => by ring))
    (by intro v u u'; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by intro c v u; simp [Finset.mul_sum, Complex.mul_im, Complex.mul_re]; exact Finset.sum_congr rfl (fun i _ => by ring))

theorem imForm_apply (n : ℕ) (ρ : ℝ) (v u : Fin n → ℂ) :
    imForm n ρ v u = (∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (u j)).im := rfl

theorem imForm_nondeg (n : ℕ) (ρ : ℝ) (hρ : ρ ≠ 0) (v : Fin n → ℂ)
    (h : ∀ u, imForm n ρ v u = 0) : v = 0 := by
  have h1 := h (Complex.I • v)
  rw [imForm_apply, Complex.im_sum] at h1
  have hterm : ∀ j, ((ρ : ℂ) * v j * starRingEnd ℂ ((Complex.I • v) j)).im = -ρ * Complex.normSq (v j) := by
    intro j
    simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply]; ring
  simp_rw [hterm, ← Finset.mul_sum] at h1
  have hs : ∑ j, Complex.normSq (v j) = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (neg_eq_zero.mp h2) hρ
    · exact h2
  funext j
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))).mp hs j (Finset.mem_univ _)
  simpa using this

theorem mem_range_of_int_pairing (E : Type) [Field E] [NumberField E] (n : ℕ)
    (Φ : E →ₗ[ℚ] (Fin n → ℂ)) (L : Set E) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hspan : Submodule.span ℝ (Φ '' L) = ⊤)
    (hrat : ∀ x y : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ y j)).im = q)
    (w : Fin n → ℂ)
    (hw : ∀ x ∈ L, ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m) :
    ∃ x : E, w = Φ x := by
  set B := imForm n ρ with hB
  obtain ⟨t, htsub, htspan, htli⟩ := exists_linearIndependent ℝ (Φ '' L)
  have htfin : t.Finite := htli.setFinite
  haveI : Fintype t := htfin.fintype
  have hts : Submodule.span ℝ t = ⊤ := htspan.trans hspan

  have hvan : ∀ v, (∀ k : t, B v k = 0) → v = 0 := by
    intro v hv
    apply imForm_nondeg n ρ hρ v
    intro u
    have hle : Submodule.span ℝ t ≤ LinearMap.ker (B v) :=
      Submodule.span_le.mpr (fun k hk => by simpa using hv ⟨k, hk⟩)
    have hu : u ∈ LinearMap.ker (B v) := hle (hts ▸ Submodule.mem_top)
    simpa using hu

  have hpre : ∀ k : t, ∃ x ∈ L, Φ x = k := fun k => htsub k.2
  choose xk hxkL hxk using hpre
  choose q hq using hrat
  let Q : Matrix t t ℚ := fun k j => q (xk k) (xk j)
  have hBQ : ∀ k j : t, B k j = (Q k j : ℝ) := by
    intro k j
    rw [hB, imForm_apply, ← hxk k, ← hxk j]; exact hq _ _
  choose m hm using fun j : t => hw (xk j) (hxkL j)
  have hBm : ∀ j : t, B w j = (m j : ℝ) := by
    intro j; rw [hB, imForm_apply, ← hxk j]; exact hm j

  have hinj : Function.Injective (Matrix.vecMulLinear Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hz : ∑ k, (c k : ℝ) • (k : Fin n → ℂ) = 0 := by
      apply hvan
      intro j
      have hj := congrFun hc j
      simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Pi.zero_apply] at hj
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hBQ]
      exact_mod_cast hj
    have := (Fintype.linearIndependent_iff.mp htli) (fun k => (c k : ℝ)) hz
    funext k; exact_mod_cast this k
  have hsurj := (LinearMap.injective_iff_surjective.mp hinj)
  obtain ⟨c, hc⟩ := hsurj (fun j => (m j : ℚ))
  refine ⟨∑ k, c k • xk k, ?_⟩
  rw [← sub_eq_zero]
  apply hvan
  intro j
  have hj := congrFun hc j
  simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct] at hj
  rw [map_sub, LinearMap.sub_apply, hBm, map_sum, map_sum, LinearMap.sum_apply]
  simp only [map_smul, ← Rat.cast_smul_eq_qsmul ℝ, hxk, map_smul, LinearMap.smul_apply, smul_eq_mul, hBQ]
  rw [sub_eq_zero]
  exact_mod_cast hj.symm

end GlobalTheory.CxDescent

import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt

noncomputable section

namespace GlobalTheory.SupNormExample

open Formalism.L2.Pj

variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

def conjAt (σ : K →+* ℂ) : CAt σ →ₐ[K] CAt ((starRingEnd ℂ).comp σ) :=
  { (starRingEnd ℂ : ℂ →+* ℂ) with commutes' := fun _ => rfl }

theorem ptNorm_conj (σ : K →+* ℂ) (fn : pts (CAt σ) → ι → ℝ)
    (fn' : pts (CAt ((starRingEnd ℂ).comp σ)) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) (z : pts (CAt ((starRingEnd ℂ).comp σ)))
    (hv : evalAt pts mapR f z = conjAt σ (evalAt pts mapR f y)) (hn : ∀ i, |fn' z i| = |fn y i|) :
    ptNorm pts mapR _ fn' e f z = ptNorm pts mapR σ fn e f y := by
  unfold ptNorm
  rw [hv]
  simp only [hn]
  congr 1
  exact RCLike.norm_conj (K := ℂ) _

theorem bddAt_of_fnorm_zero (σ : K →+* ℂ) (e : ι → ℕ) (i : ι) (hi : e i ≠ 0) (f : Rules pts) :
    BddAt pts mapR σ (fun _ _ => 0) e f ∧ supAt pts mapR σ (fun _ _ => 0) e f = 0 := by
  have h : ∀ y, ptNorm pts mapR σ (fun _ _ => 0) e f y = 0 := fun y => by
    unfold ptNorm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩; exact (h y).le
  · unfold supAt; simp [h]

theorem exists_fnorm_small (σ : K →+* ℂ) (e : ι → ℕ) (i : ι) (hi : e i ≠ 0) (f : Rules pts) :
    ∃ fnorm : pts (CAt σ) → ι → ℝ, (∀ y j, 0 < fnorm y j) ∧ BddAt pts mapR σ fnorm e f ∧
      supAt pts mapR σ fnorm e f ≤ 1 := by
  classical
  let c : pts (CAt σ) → ℝ := fun y => cabs (evalAt pts mapR f y)
  have hc : ∀ y, 0 ≤ c y := fun y => norm_nonneg _
  have h : ∀ y, ptNorm pts mapR σ (fun y _ => 1 + c y) e f y ≤ 1 := fun y => by
    have hp : 0 < 1 + c y := by linarith [hc y]
    have h1 : (1 + c y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hc y])
    have h0 : 0 ≤ (1 + c y)⁻¹ := inv_nonneg.2 hp.le
    show c y * ∏ j, |1 + c y|⁻¹ ^ e j ≤ 1
    rw [abs_of_pos hp, Finset.prod_pow_eq_pow_sum]
    have hs : 1 ≤ ∑ j, e j :=
      (Nat.one_le_iff_ne_zero.2 hi).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    have h2 : (1 + c y)⁻¹ ^ ∑ j, e j ≤ (1 + c y)⁻¹ := by
      simpa using pow_le_pow_of_le_one h0 h1 hs
    refine (mul_le_mul_of_nonneg_left h2 (hc y)).trans ?_
    rw [← div_eq_mul_inv, div_le_one hp]; linarith
  refine ⟨fun y _ => 1 + c y, fun y _ => by linarith [hc y], ⟨1, ?_⟩, Real.iSup_le h zero_le_one⟩
  rintro _ ⟨y, rfl⟩; exact h y

end GlobalTheory.SupNormExample

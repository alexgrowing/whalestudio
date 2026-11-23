import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelationRowStepsFunctionalEigenStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselColumnStepsFunctionalEigenStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorBlockLinearMapIntertwineStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixPicksSplitCasimirEigencomponentStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
private theorem qminor_cast {M : Type} [AddCommGroup M] [Module ℂ M] {n a b : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (h : a = b) (f g : Fin b → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E (fun i : Fin a => f (Fin.cast h i)) (fun i : Fin a => g (Fin.cast h i)) u
      = Formalism.REAL.qminor E f g u := by
  subst h
  rfl
end GlobalTheory

namespace GlobalTheory

theorem capelli_projector_entry_value : ∀ (M Wp : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → ∀ (mu : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (Pop : Fin k → Fin k → Wp → Wp), Function.Injective mu → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ i j v, l (E ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) v) = Pop i j (l v)) → (∀ (w : ℂ) (x : Wp), Formalism.FourierDecayAlt.Q.qmF Pop id id w x = (∏ i ∈ Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • x) → ∀ s, ∃ c : ℂ, ‖c‖ = (if r = 0 then 1 else τ ^ 2) * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ (v : M) (y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → M), (∀ t, splitCas E (y t) = ((-mu t + (1 - (((2 * r + k + 1) : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∑ t, y t = Pi.single (Fin.last (2 * r + k)) v → l (y s (if r = 0 then Fin.last (2 * r + k) else 0)) = c • l v := by
  intro M Wp _ _ _ _ k r E l p τ hk hE hp mu u Pop hmu hq hP hW s
  set D : ℂ := ∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s) with hD
  set N : ℂ := ∏ i ∈ Icc 1 k, (-(mu s : ℂ) + 1 / 2 + (u i : ℂ)) with hN
  have hDn : ‖D‖ = ∏ t ∈ univ.erase s, |mu s - mu t| := by
    rw [hD, norm_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hNn : ‖N‖ = ∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i| := by
    rw [hN, norm_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    have : (-(mu s : ℂ) + 1 / 2 + (u t : ℂ)) = ((-(mu s - 1 / 2 - u t) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hD0 : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro t ht h
    have h1 : mu t = mu s := by exact_mod_cast sub_eq_zero.mp h
    exact (Finset.mem_erase.mp ht).1 (hmu h1)
  have hinj : Function.Injective (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    intro a b h
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)
  have hblock : ∀ v, l (Formalism.REAL.qminor E (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (-(mu s : ℂ) + (k : ℂ) / 2) v) = N • l v := by
    intro v
    rw [GlobalTheory.T.quantumMinor_block_linearMap_intertwine M Wp _ k E l _ Pop hinj hP, hW, hN]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hcof : ∀ (v : M) (y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → M), (∀ t, splitCas E (y t) = ((-mu t + (1 - (((2 * r + k + 1) : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∑ t, y t = Pi.single (Fin.last (2 * r + k)) v → ∀ i : Fin (2 * r + k + 1),
      D • l (y s i) = ((-1 : ℂ) ^ (i.val + (2 * r + k))) • l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove i) (-(mu s : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) v) := by
    intro v y hy hs i
    have h := GlobalTheory.T.capelliComatrix_picks_splitCasimir_eigencomponent M (2 * r + k) E mu y hE hq hy s i
    have hj : ∀ j, ∑ t, y t j = (Pi.single (Fin.last (2 * r + k)) v : Fin (2 * r + k + 1) → M) j := by
      intro j
      rw [← hs, Finset.sum_apply]
    rw [Finset.sum_eq_single (Fin.last (2 * r + k))] at h
    · rw [hj, Pi.single_eq_same] at h
      rw [← map_smul, ← map_smul, hD, ← h]
      rfl
    · intro j _ hne
      rw [hj, Pi.single_eq_of_ne hne]
      simp
    · simp
  by_cases hr : r = 0
  · refine ⟨D⁻¹ * N, ?_, ?_⟩
    · rw [norm_mul, norm_inv, hDn, hNn, if_pos hr]; ring
    · intro v y hy hs
      rw [if_pos hr]
      have h := hcof v y hy hs (Fin.last _)
      subst hr
      have hm : Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * 0 + k))) (Fin.succAbove (Fin.last (2 * 0 + k))) (-(mu s : ℂ) + ((2 * 0 + k : ℕ) : ℂ) / 2) = Formalism.REAL.qminor E (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1)))
          (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1))) (-(mu s : ℂ) + (k : ℂ) / 2) := by
        have := qminor_cast E (show k = 2 * 0 + k by omega) (Fin.succAbove (Fin.last (2 * 0 + k))) (Fin.succAbove (Fin.last (2 * 0 + k))) (-(mu s : ℂ) + (k : ℂ) / 2)
        have e : (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1))) = fun i => Fin.succAbove (Fin.last (2 * 0 + k)) (Fin.cast (show k = 2 * 0 + k by omega) i) := by
          funext i
          apply Fin.ext
          simp
        rw [e, this]
        simp
      rw [hm, hblock] at h
      have hs1 : ((-1 : ℂ) ^ ((Fin.last (2 * 0 + k)).val + (2 * 0 + k))) = 1 := by
        rw [Fin.val_last, ← two_mul, pow_mul]; simp
      rw [hs1, one_smul] at h
      rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hD0, one_smul]
  · have hr1 : 1 ≤ r := by omega
    obtain ⟨c1, hc1, h1⟩ := GlobalTheory.T.glRelation_row_steps_functional_eigen M Wp k r E l p τ hk hE hp hr1
    obtain ⟨c2, hc2, h2⟩ := GlobalTheory.T.besselColumnSteps_functional_eigen M Wp k r E l p τ hk hE hp hr1
    refine ⟨D⁻¹ * ((-1 : ℂ) ^ (2 * r + k) * (c1 * (c2 * N))), ?_, ?_⟩
    · rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_mul, hDn, hNn, if_neg hr, hc1, hc2, norm_pow]
      simp only [norm_neg, norm_one, one_pow]
      ring
    · intro v y hy hs
      rw [if_neg hr]
      have h := hcof v y hy hs 0
      have e : (-(mu s : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) - (r : ℂ) = -(mu s : ℂ) + (k : ℂ) / 2 := by
        push_cast; ring
      rw [h1, h2, e, hblock, Fin.val_zero, zero_add] at h
      rw [mul_smul, mul_smul, mul_smul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hD0, one_smul]

end GlobalTheory

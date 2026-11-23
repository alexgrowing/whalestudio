import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceSubstitution
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ExtensionSingularValues

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.Proof.ColumnInclusionRenaming

open GlobalTheory.IndefiniteRowSideFullHecke

theorem fockS_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    fockS (rename e f) (rename e g) = fockS f g := by
  classical
  unfold fockS
  rw [support_rename_of_injective he, Finset.sum_image (fun _ _ _ _ h => Finsupp.mapDomain_injective he h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]
  congr 2
  unfold mfact
  rw [Finsupp.mapDomain_support_of_injective he, Finset.prod_image (fun _ _ _ _ h => he h)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.mapDomain_apply he]

def colIncl {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (r : ℕ) : Fin r × Fin n₀ → Fin r × Fin n₁ :=
  fun v => (v.1, Fin.castLE h v.2)

theorem rename_lpMinor {n₀ n₁ r : ℕ} (h : n₀ ≤ n₁) (s : ℕ) (hr : s ≤ r) (hs : s ≤ n₀) :
    rename (colIncl h r) (lpMinor ℂ s hr hs) = lpMinor ℂ s hr (hs.trans h) := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [colIncl]

theorem rename_hw {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ) :
    rename (colIncl h n₁) (hw ℂ h ν) = hw ℂ (le_refl n₁) (rowNu (r := n₁) ν) := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro s _ hs
    have hs' : ¬ s.val < n₀ := fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩
    have : rowNu (r := n₁) ν s = 0 := by simp [rowNu, hs']
    rw [this, Nat.zero_sub, pow_zero]
  · intro s _
    rw [map_pow, rename_lpMinor]
    have e1 : rowNu (r := n₁) ν (Fin.castLE h s) = ν s := by simp [rowNu]
    have e2 : nuNext (rowNu (r := n₁) ν) (Fin.castLE h s) = nuNext ν s := by
      unfold nuNext rowNu
      by_cases h1 : s.val + 1 < n₀
      · have h2 : s.val + 1 < n₁ := by omega
        simp [h1, h2]
      · simp [h1]
    rw [e1, e2]
    rfl

end GlobalTheory.Proof.ColumnInclusionRenaming

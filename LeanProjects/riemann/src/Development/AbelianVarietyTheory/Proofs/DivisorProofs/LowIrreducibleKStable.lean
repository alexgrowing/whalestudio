import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowStable

theorem X_mul_pderiv_totalDegree_le {σ : Type} (u v : σ) (g : MvPolynomial σ ℂ) :
    (X u * pderiv v g).totalDegree ≤ g.totalDegree := by
  classical
  have key : ∀ m ∈ (pderiv v g).support, (m.sum fun _ e => e) + 1 ≤ g.totalDegree := by
    intro m hm
    have hc : coeff (m + Finsupp.single v 1) g ≠ 0 := by
      rw [mem_support_iff, coeff_pderiv] at hm
      intro h
      rw [h, zero_mul] at hm
      exact hm rfl
    have h1 := le_totalDegree (mem_support_iff.2 hc)
    have h2 : ((m + Finsupp.single v 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [h2] at h1
    exact h1
  by_cases h0 : pderiv v g = 0
  · rw [h0, mul_zero, totalDegree_zero]; exact Nat.zero_le _
  · obtain ⟨m, hm⟩ := (support_nonempty).2 h0
    have hm1 := key m hm
    have hle : (pderiv v g).totalDegree ≤ g.totalDegree - 1 :=
      Finset.sup_le fun m' hm' => by have := key m' hm'; show (m'.sum fun _ e => e) ≤ _; omega
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    omega

theorem omE_mem_restrictTotalDegree {P Q R S : ℕ} (D : ℕ) (u v : Ln P Q R S) (h : linePos u = linePos v)
    (g : Pol P Q R S) (hg : g ∈ restrictTotalDegree (Ln P Q R S) ℂ D) :
    omE u v g ∈ restrictTotalDegree (Ln P Q R S) ℂ D := by
  have hN := (mem_restrictTotalDegree _ _ _).1 hg
  have hXd : ∀ a b : Ln P Q R S, X a * pderiv b g ∈ restrictTotalDegree (Ln P Q R S) ℂ D :=
    fun a b => (mem_restrictTotalDegree _ _ _).2 ((X_mul_pderiv_totalDegree_le a b g).trans hN)
  cases hu : linePos u
  · rw [GlobalTheory.CompactHarm.omE_nn u v hu (h ▸ hu) g]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (hXd v u)) (Submodule.smul_mem _ _ hg)
  · rw [GlobalTheory.CompactHarm.omE_pp u v hu (h ▸ hu) g]
    exact Submodule.add_mem _ (hXd u v) (Submodule.smul_mem _ _ hg)

theorem fockAct2_apply_eq {P Q R S : ℕ} (Z : Mat R S) (g : Pol P Q R S) :
    fockAct2 P Q R S Z g = ∑ c, ∑ d, Z c d • ∑ a, omE (a, c) (a, d) g := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have : Matrix.single c d (Z c d) = Z c d • (Eab c d : Mat R S) := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply, fockAct2_Eab, LinearMap.sum_apply]

theorem fockAct2_mem_restrictTotalDegree {P Q R S : ℕ} (D : ℕ) (Z : Mat R S) (hZ : IsKC Z)
    (g : Pol P Q R S) (hg : g ∈ restrictTotalDegree (Ln P Q R S) ℂ D) :
    fockAct2 P Q R S Z g ∈ restrictTotalDegree (Ln P Q R S) ℂ D := by
  rw [fockAct2_apply_eq]
  refine Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ => ?_
  by_cases hcd : sameBlock c d
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
    refine omE_mem_restrictTotalDegree D _ _ ?_ g hg
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      first | rfl | exact absurd hcd (by simp [sameBlock])
  · rw [hZ c d hcd, zero_smul]
    exact Submodule.zero_mem _

theorem lowOne_stable : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k →
    x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsKC Z →
    ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k'),
    Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') := by
  intro P Q R S x k k' _ _ Z hZ f hf
  rw [GlobalTheory.KFixIrr.lowOne, Submodule.mem_inf] at hf ⊢
  refine ⟨?_, fockAct2_mem_restrictTotalDegree _ Z hZ f hf.2⟩
  rw [GlobalTheory.KFixIrr.mem_chiOne] at hf ⊢
  intro X hX
  have hc := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.2 X Z) f
  rw [Module.End.mul_apply, Module.End.mul_apply] at hc
  rw [hc, hf.1 X hX, map_smul]

end GlobalTheory.LowStable

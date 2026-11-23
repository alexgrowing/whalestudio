import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowDiv_raise_eq_zero (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) k) (hf : f ∈ dualWeyl k N N ν)
    (hwt : IsWeightedHomogeneous (rowW N N) f ν) (a b : Fin N) (hab : a < b) (j : ℕ) (hj : 1 ≤ j) :
    rowDiv k a b j f = 0 := by
  classical
  by_contra hne
  have hg : rowDiv k a b j f ∈ dualWeyl k N N ν := rowDivStable k N N ν a b j f hf
  have hZ : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) f (fun i => (ν i : ℤ)) := by
    intro d hd
    funext i
    rw [GlobalTheory.LvT.KerLat.weight_rowZ, hwt hd]
  have hsh := GlobalTheory.LvT.KerLat.rowDiv_shift k (fun i => (ν i : ℤ)) a b j f hZ
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have e := hsh hm
  have dom := (GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ hg m (mem_support_iff.mpr hm)).1 (a.val + 1)
  have hrow : ∀ i, ((rowDeg m i : ℕ) : ℤ) = (ν i : ℤ) + (j : ℤ) * ((Pi.single a (1:ℤ) : Fin N → ℤ) i - (Pi.single b (1:ℤ) : Fin N → ℤ) i) := by
    intro i
    have := congrFun e i
    rw [GlobalTheory.LvT.KerLat.weight_rowZ, GlobalTheory.LvT.KerLat.weight_rowW] at this
    rw [this]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcast : ((∑ i : Fin N with i.val < a.val + 1, rowDeg m i : ℕ) : ℤ) =
      ((∑ i : Fin N with i.val < a.val + 1, ν i : ℕ) : ℤ) + j := by
    push_cast
    simp only [hrow]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    have ha : (∑ i : Fin N with i.val < a.val + 1, (Pi.single a (1:ℤ) : Fin N → ℤ) i) = 1 := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro i _ hi; simp [Pi.single_apply, hi]
      · intro h; simp at h
    have hb : (∑ i : Fin N with i.val < a.val + 1, (Pi.single b (1:ℤ) : Fin N → ℤ) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have : i ≠ b := by
        intro h; subst h
        simp at hi
        have : a.val < i.val := hab
        omega
      simp [Pi.single_apply, this]
    rw [ha, hb]; ring
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have : ((∑ i : Fin N with i.val < a.val + 1, rowDeg m i : ℕ) : ℤ) ≤
      ((∑ i : Fin N with i.val < a.val + 1, ν i : ℕ) : ℤ) := by exact_mod_cast dom
  omega

theorem hw_line_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ f ∈ dualWeyl k N N ν,
    IsWeightedHomogeneous (rowW N N) f ν → ∃ c : k, f = c • hw k le_rfl ν := by
  intro k _ N ν hν f hf hwt
  classical
  let K := AlgebraicClosure k
  let φ : k →+* K := algebraMap k K
  have hgK : map φ f ∈ dualWeyl K N N ν := dualWeylMap k K φ N N ν f hf
  have hrK : ∀ a b : Fin N, a < b → ∀ j : ℕ, 1 ≤ j → rowDiv K a b j (map φ f) = 0 := by
    intro a b hab j hj
    rw [lclosedeq_rowDiv_map, rowDiv_raise_eq_zero k N ν f hf hwt a b hab j hj, map_zero]
  obtain ⟨c, hc⟩ := hwLine K N N le_rfl ν hν (map φ f) hgK hrK
  obtain ⟨m, hm⟩ := ne_zero_iff.mp (hwNe k N N le_rfl ν)
  refine ⟨coeff m f / coeff m (hw k le_rfl ν), ?_⟩
  have hcm := congrArg (coeff m) hc
  rw [coeff_map, coeff_smul, ← lclosedeq_hw_map φ, coeff_map, smul_eq_mul] at hcm
  have hφ : φ (coeff m (hw k le_rfl ν)) ≠ 0 := (map_ne_zero φ).mpr hm
  have hcv : c = φ (coeff m f / coeff m (hw k le_rfl ν)) := by
    rw [map_div₀, hcm, mul_div_cancel_right₀ _ hφ]
  apply map_injective φ φ.injective
  rw [hc, hcv, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, lclosedeq_hw_map]

end GlobalTheory.Alc

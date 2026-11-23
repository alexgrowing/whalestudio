import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RenameSwapAtMonomial
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VdmHarm

open MvPolynomial

theorem totalDegree_pderiv_le_pred {σ : Type} (i : σ) (Q : MvPolynomial σ ℝ) :
    (pderiv i Q).totalDegree ≤ Q.totalDegree - 1 := by
  refine Finset.sup_le fun m hm => ?_
  have hc : coeff (m + Finsupp.single i 1) Q ≠ 0 := by
    rw [mem_support_iff, coeff_pderiv] at hm
    intro h
    rw [h, zero_mul] at hm
    exact hm rfl
  have h1 := le_totalDegree (mem_support_iff.2 hc)
  have h2 : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  rw [h2] at h1
  show (m.sum fun _ e => e) ≤ Q.totalDegree - 1
  omega

theorem coeff_eq_zero_of_swap {r : ℕ} {a b : Fin r} (P : MvPolynomial (Option (Fin r)) ℝ)
    (hP : rename (Option.map (Equiv.swap a b)) P = -P) (m : Option (Fin r) →₀ ℕ)
    (hm : m (some a) = m (some b)) : coeff m P = 0 := by
  have hinj : Function.Injective (Option.map (Equiv.swap a b)) := Option.map_injective (Equiv.injective _)
  have hmd : m.mapDomain (Option.map (Equiv.swap a b)) = m := by
    ext x
    have hx : Option.map (Equiv.swap a b) (Option.map (Equiv.swap a b) x) = x := by
      cases x <;> simp
    conv_lhs => rw [← hx]
    rw [Finsupp.mapDomain_apply hinj]
    rcases x with _ | i
    · rfl
    · by_cases ha : i = a
      · subst ha; simp [hm]
      · by_cases hb : i = b
        · subst hb; simp [hm]
        · simp [Equiv.swap_apply_of_ne_of_ne ha hb]
  have h := coeff_rename_mapDomain _ hinj P m
  rw [hmd, hP, coeff_neg] at h
  linarith

theorem rename_swap_vdm {r : ℕ} {a b : Fin r} (hab : a ≠ b) :
    rename (Option.map (Equiv.swap a b))
      (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (X (some i') - X (some i)) : MvPolynomial (Option (Fin r)) ℝ) =
      -(∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (X (some i') - X (some i)) : MvPolynomial (Option (Fin r)) ℝ) := by
  have h1 : (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (X (some i') - X (some i)) : MvPolynomial (Option (Fin r)) ℝ) =
      (Matrix.vandermonde (fun i : Fin r => (X (some i) : MvPolynomial (Option (Fin r)) ℝ))).det :=
    (Matrix.det_vandermonde _).symm
  have h2 : rename (Option.map (Equiv.swap a b))
      (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (X (some i') - X (some i)) : MvPolynomial (Option (Fin r)) ℝ) =
      (Matrix.vandermonde ((fun i : Fin r => (X (some i) : MvPolynomial (Option (Fin r)) ℝ)) ∘ Equiv.swap a b)).det := by
    rw [Matrix.det_vandermonde]
    simp [map_prod]
  have h3 : Matrix.vandermonde ((fun i : Fin r => (X (some i) : MvPolynomial (Option (Fin r)) ℝ)) ∘ Equiv.swap a b) =
      (Matrix.vandermonde (fun i : Fin r => (X (some i) : MvPolynomial (Option (Fin r)) ℝ))).submatrix
        (Equiv.swap a b) id := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [h2, h3, Matrix.det_permute, Equiv.Perm.sign_swap hab, ← h1]
  simp

theorem totalDegree_vdm_le (r : ℕ) :
    (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (X (some i') - X (some i)) : MvPolynomial (Option (Fin r)) ℝ).totalDegree ≤
      r * (r - 1) / 2 := by
  refine (totalDegree_finsetProd _ _).trans ?_
  have h (i : Fin r) : (∏ i' ∈ Finset.Ioi i, (X (some i') - X (some i)) : MvPolynomial (Option (Fin r)) ℝ).totalDegree ≤
      (r - 1 - (i : ℕ)) := by
    refine (totalDegree_finsetProd _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => (1 : ℕ)) fun i' _ => (totalDegree_sub _ _).trans (by simp [totalDegree_X])).trans ?_
    simp [Fin.card_Ioi]
  refine (Finset.sum_le_sum fun i _ => h i).trans (le_of_eq ?_)
  have e : ∑ i : Fin r, (r - 1 - (i : ℕ)) = ∑ i : Fin r, (i : ℕ) := by
    rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin r => (i : ℕ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Fin.val_rev]
    omega
  rw [e, Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem vdm_pderiv_sum_and_laplacian : ∀ r : ℕ, ∑ a : Fin r, MvPolynomial.pderiv (some a) (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)) : MvPolynomial (Option (Fin r)) ℝ) = 0 ∧ ∑ a : Fin r, MvPolynomial.pderiv (some a) (MvPolynomial.pderiv (some a) (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)) : MvPolynomial (Option (Fin r)) ℝ)) = 0 := by
  intro r
  constructor
  · have hmul : ∀ p q : MvPolynomial (Option (Fin r)) ℝ,
        ∑ a : Fin r, MvPolynomial.pderiv (some a) p = 0 → ∑ a : Fin r, MvPolynomial.pderiv (some a) q = 0 →
        ∑ a : Fin r, MvPolynomial.pderiv (some a) (p * q) = 0 := by
      intro p q hp hq
      simp only [Derivation.leibniz, Finset.sum_add_distrib, ← Finset.smul_sum, hp, hq, smul_zero, add_zero]
    refine Finset.prod_induction _ (fun p => ∑ a : Fin r, MvPolynomial.pderiv (some a) p = 0) hmul
      (by simp) fun i _ => ?_
    refine Finset.prod_induction _ (fun p => ∑ a : Fin r, MvPolynomial.pderiv (some a) p = 0) hmul
      (by simp) fun i' _ => ?_
    simp [Pi.single_apply]
  · set V : MvPolynomial (Option (Fin r)) ℝ :=
      ∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)) with hV
    set L := ∑ a : Fin r, MvPolynomial.pderiv (some a) (MvPolynomial.pderiv (some a) V) with hL
    have halt : ∀ a b : Fin r, a ≠ b → MvPolynomial.rename (Option.map (Equiv.swap a b)) L = -L := by
      intro a b hab
      have hinj : Function.Injective (Option.map (Equiv.swap a b)) := Option.map_injective (Equiv.injective _)
      have hVs : MvPolynomial.rename (Option.map (Equiv.swap a b)) V = -V := rename_swap_vdm hab
      rw [hL, map_sum]
      simp only [← MvPolynomial.pderiv_rename hinj, hVs, map_neg, Option.map_some]
      rw [← Finset.sum_neg_distrib]
      exact Equiv.sum_comp (Equiv.swap a b) (fun c => -(MvPolynomial.pderiv (some c) (MvPolynomial.pderiv (some c) V)))
    have hdegV : V.totalDegree ≤ r * (r - 1) / 2 := totalDegree_vdm_le r
    by_cases h0 : V.totalDegree = 0
    · have h1 : ∀ a : Fin r, MvPolynomial.pderiv (some a) V = 0 := fun a => by
        rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 h0, MvPolynomial.pderiv_C]
      simp [hL, h1]
    · have hdegL : L.totalDegree ≤ V.totalDegree - 2 := by
        refine MvPolynomial.totalDegree_finsetSum_le fun a _ => ?_
        have h1 := totalDegree_pderiv_le_pred (some a) (MvPolynomial.pderiv (some a) V)
        have h2 := totalDegree_pderiv_le_pred (some a) V
        omega
      ext m
      rw [MvPolynomial.coeff_zero]
      by_contra hc
      have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.2 hc)
      have hsum : (m.sum fun _ e => e) = m none + ∑ i : Fin r, m (some i) := by
        rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_option]
      by_cases hinj : Function.Injective (fun i : Fin r => m (some i))
      · have hN := GlobalTheory.FlagAnti.le_sum_of_injective hinj
        generalize r * (r - 1) / 2 = N at hN hdegV
        omega
      · simp only [Function.Injective, not_forall] at hinj
        obtain ⟨a, b, h, hne⟩ := hinj
        exact hc (coeff_eq_zero_of_swap L (halt a b hne) m h)

end GlobalTheory.VdmHarm

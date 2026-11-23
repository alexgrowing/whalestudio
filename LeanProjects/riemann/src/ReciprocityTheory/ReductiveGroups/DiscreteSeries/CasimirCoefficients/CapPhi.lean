import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiCapelliStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPhiA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowCol
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Central

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace CapPhi

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

lemma capelliC_negT {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] (E : Fin n → Fin n → 𝒰) (x : ℂ) :
    capelliC (fun a b => -E b a) x = (-1) ^ n * rminor E id id ((n : ℂ) - 1 - x) := by
  unfold capelliC cminor rminor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← (Int.cast_commute _ _).eq, mul_assoc]
  congr 1
  have hf : (fun j : Fin n => capEntry (fun a b => -E b a) (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j)) =
      Neg.neg ∘ fun j : Fin n => capEntry E ((n : ℂ) - 1 - x - ((n : ℕ) : ℂ) + 1 + ((j : ℕ) : ℂ)) (id j)
        (id (σ j)) := by
    funext j
    simp only [capEntry, id, Function.comp]
    by_cases h : σ j = j
    · simp only [h, if_true]
      rw [neg_add, ← map_neg]
      congr 2
      ring
    · have h' : ¬ j = σ j := fun e => h e.symm
      simp only [if_neg h, if_neg h', add_zero]
  rw [hf, ← List.map_ofFn, List.prod_map_neg, List.length_ofFn]

def negE : Fin n → Fin n → Module.End ℂ (smoothS n) := fun a b => eOp (-(Matrix.single a b (1 : ℂ)))

lemma single_mul_single' (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro x _
    split_ifs <;> simp_all

lemma isGlRep_negE : IsGlRep (negE (n := n)) := by
  apply isGlRep_eOp
  intro a b c d
  simp only [neg_mul_neg, single_mul_single']
  split_ifs <;> abel

lemma negE_apply (a b : Fin n) (G : smoothS n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    ((negE a b G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z = -Lhol (Matrix.single a b 1) G z := by
  show ltOp (-(Matrix.single a b (1 : ℂ))) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z = _
  rw [ltOp_of_mem _ hz]
  show fderiv ℂ (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z (-(Matrix.single a b (1 : ℂ)) * z) =
    -fderiv ℂ (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z (Matrix.single a b 1 * z)
  rw [Matrix.neg_mul, map_neg]

lemma negE_apply_out (a b : Fin n) (G : smoothS n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∉ OmegaSet n) :
    ((negE a b G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z = 0 := by
  exact ltOp_of_not_mem _ hz

def phiS (μ : Fin n → ℤ) : smoothS n :=
  ⟨(OmegaSet n).indicator (PhiM μ),
    (show ContDiffOn ℂ ∞ (PhiM μ) (OmegaSet n) from fun _ hz => (contDiffAt_phiM μ hz).contDiffWithinAt).congr
      fun _ hz => Set.indicator_of_mem hz _⟩

lemma phiS_eqOn (μ : Fin n → ℤ) : Set.EqOn (PhiM μ) ((phiS μ : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (OmegaSet n) :=
  fun _ hz => (Set.indicator_of_mem hz (PhiM μ)).symm

lemma phiS_up (μ : Fin n → ℤ) (a b : Fin n) (hab : a < b) : (-negE b a) (phiS μ) = 0 := by
  apply Subtype.ext
  funext z
  show -((negE b a (phiS μ) : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z = 0
  by_cases hz : z ∈ OmegaSet n
  · rw [negE_apply _ _ _ hz, ← lhol_congr (phiS_eqOn μ) hz, lhol_phiM_lower μ hab hz, neg_zero, neg_zero]
  · rw [negE_apply_out _ _ _ hz, neg_zero]

lemma phiS_diag (μ : Fin n → ℤ) (a : Fin n) : (-negE a a) (phiS μ) = (-(μ a : ℂ)) • phiS μ := by
  apply Subtype.ext
  funext z
  show -((negE a a (phiS μ) : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z =
    (-(μ a : ℂ)) • ((phiS μ : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z
  by_cases hz : z ∈ OmegaSet n
  · rw [negE_apply _ _ _ hz, ← lhol_congr (phiS_eqOn μ) hz, lhol_phiM_diag μ a hz, ← phiS_eqOn μ hz,
      smul_eq_mul]
    ring
  · rw [negE_apply_out _ _ _ hz]
    show -(0 : ℂ) = (-(μ a : ℂ)) • (OmegaSet n).indicator (PhiM μ) z
    rw [Set.indicator_of_notMem hz, smul_zero, neg_zero]

lemma capelliC_phiS (μ : Fin n → ℤ) (u : ℂ) :
    capelliC (negE (n := n)) u (phiS μ) =
      ((-1) ^ n * ∏ a : Fin n, ((n : ℂ) - 1 - u + -(μ a : ℂ) - ((a : ℕ) : ℂ))) • phiS μ := by
  have hw := capelliC_hw (fun a b => -negE (n := n) b a) (fun a => -(μ a : ℂ)) (phiS μ)
    ((n : ℂ) - 1 - u) (phiS_up μ) (phiS_diag μ)
  rw [capelliC_negT, sub_sub_cancel] at hw
  have hR : capelliC (negE (n := n)) u = rminor (negE (n := n)) id id u :=
    cminor_eq_rminor (negE (n := n)) isGlRep_negE id id u
  have hm : ∀ (A : Module.End ℂ (smoothS n)) (v : smoothS n), ((-1) ^ n * A) v = ((-1 : ℂ) ^ n) • A v := by
    intro A v
    rw [show ((-1 : Module.End ℂ (smoothS n))) ^ n = algebraMap ℂ _ ((-1 : ℂ) ^ n) by simp,
      Module.End.mul_apply, Module.algebraMap_end_apply]
  rw [hm] at hw
  rw [hR, mul_smul, ← hw, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

lemma top_eqOn (x : ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (h : Set.EqOn F G (OmegaSet n)) :
    Set.EqOn (Formalism.QuantumDeterminants.Top negL x a b F) ((capEntry negE x a b G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ)
      (OmegaSet n) := by
  intro z hz
  have hF : F z = (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z := h hz
  have hL : Lhol (Matrix.single a b 1) F z = Lhol (Matrix.single a b 1) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
    show fderiv ℂ F z _ = fderiv ℂ (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z _
    rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (isOpen_omega.mem_nhds hz) h)]
  have hN := negE_apply a b G hz
  simp only [Formalism.QuantumDeterminants.Top, negL, capEntry, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  split_ifs with hab
  · simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hN, hF, hL, smul_eq_mul]
    ring
  · simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply, hN, hL, zero_add, add_zero]

lemma fold_eqOn : ∀ (p : ℕ) (T : Fin p → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (A : Fin p → Module.End ℂ (smoothS n)),
    (∀ i (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn (T i F) ((A i G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n)) →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn ((List.ofFn T).foldr (fun t h => t h) F)
        ((((List.ofFn A).prod) G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n)
  | 0, T, A, _, F, G, h => by simpa using h
  | p + 1, T, A, hTA, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact hTA 0 _ _ (fold_eqOn p (fun i => T i.succ) (fun i => A i.succ) (fun i => hTA i.succ) F G h)

lemma qdet_eq (u : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n) (h : Set.EqOn F G (OmegaSet n))
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Formalism.QuantumDeterminants.qdetOp negL u F z = ((capelliC (negE (n := n)) u G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
  unfold Formalism.QuantumDeterminants.qdetOp Formalism.QuantumDeterminants.qminorOp capelliC cminor
  simp only [Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key := fold_eqOn n (fun k : Fin n => Formalism.QuantumDeterminants.Top negL (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k))
    (fun j : Fin n => capEntry (negE (n := n)) (u - ((j : ℕ) : ℂ)) (id (σ j)) (id j))
    (fun i F' G' h' => top_eqOn _ _ _ F' G' h') F G h hz
  rw [Pi.smul_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, Int.cast_smul_eq_zsmul]
  exact congrArg _ key

end CapPhi

open CapPhi in
theorem cap_phiM (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) (Y : ℂ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    Formalism.QuantumDeterminants.qdetOp negL (Y + ((n : ℂ) - 1) / 2) (PhiM μ) z =
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y * PhiM μ z := by
  rw [qdet_eq (Y + ((n : ℂ) - 1) / 2) (PhiM μ) (phiS μ) (phiS_eqOn μ) hz, capelliC_phiS,
    Submodule.coe_smul, Pi.smul_apply, ← phiS_eqOn μ hz, smul_eq_mul]
  congr 1
  have hfac : ∀ a : Fin n, ((n : ℂ) - 1 - (Y + ((n : ℂ) - 1) / 2) + -(μ a : ℂ) - ((a : ℕ) : ℂ)) =
      (-1) * (Y + (lam a : ℂ)) := by
    intro a
    have h1 : (μ a : ℝ) = lam a + (((n : ℝ) - 1) / 2 - (a : ℕ)) := hμ a
    have h2 : (μ a : ℂ) = (lam a : ℂ) + (((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) := by
      have h3 := congrArg (fun x : ℝ => (x : ℂ)) h1
      push_cast at h3
      linear_combination h3
    rw [h2]
    ring
  unfold Formalism.QuantumDeterminants.capP
  simp only [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_assoc, ← mul_pow]
  norm_num

end ReciprocityTheory.ChartRestriction.DS.S7

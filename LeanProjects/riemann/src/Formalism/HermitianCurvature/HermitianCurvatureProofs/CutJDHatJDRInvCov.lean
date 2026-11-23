import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvDefs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal Formalism.FourierDecayAlt.P.FourTermExpansion
  Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_right (X S x : Mat k r) (f : Mat k r → E) (h1 : S * S⁻¹ = 1) (h2 : S⁻¹ * S = 1) :
    RdV X (fun y => f (y * S)) x = RdV (S⁻¹ * X * S) f (x * S) := by
  unfold RdV
  congr 1
  funext t
  have e1 : ((t : ℂ) • (S⁻¹ * X * S)) = S⁻¹ * ((t : ℂ) • X) * S := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, Formalism.QuantumDeterminants.ioh_exp_conj S⁻¹ S _ h1 h2]
  show f (x * NormedSpace.exp ((t : ℂ) • X) * S) = f (x * S * (S⁻¹ * NormedSpace.exp ((t : ℂ) • X) * S))
  congr 1
  calc x * NormedSpace.exp ((t : ℂ) • X) * S
      = x * (S * S⁻¹) * NormedSpace.exp ((t : ℂ) • X) * S := by rw [h1, Matrix.mul_one]
    _ = x * S * (S⁻¹ * NormedSpace.exp ((t : ℂ) • X) * S) := by simp only [Matrix.mul_assoc]

theorem rdV_left (X A x : Mat k r) (f : Mat k r → E) :
    RdV X (fun y => f (A * y)) x = RdV X f (A * x) := by
  unfold RdV
  simp only [Matrix.mul_assoc]

theorem EZ_right (S : Mat k r) (hS : S ∈ GV k r) (f : Mat k r → E) (a b : Fin (2 * r + k + 1)) (x : Mat k r) :
    EZ (Msg k r a b) (fun y => f (y * S)) x = EZ (Mc S a b) f (x * S) := by
  have h := congrFun (congrFun (congrFun (congrFun (EHc_eq_LT (E := E) S hS) a) b) f) (x * S)
  refine Eq.trans ?_ h
  obtain ⟨h1, h2⟩ := gv_inv hS
  show RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) (fun y => f (y * S)) x +
      Complex.I • RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) (fun y => f (y * S)) x = _
  rw [rdV_right _ _ _ _ h1 h2, rdV_right _ _ _ _ h1 h2]
  rfl

theorem EZ_left (A : Mat k r) (Z : Mat k r) (f : Mat k r → E) (x : Mat k r) :
    EZ Z (fun y => f (A * y)) x = EZ Z f (A * x) := by
  unfold EZ
  rw [rdV_left, rdV_left]

theorem fold_right (S : Mat k r) (hS : S ∈ GV k r) (f : Mat k r → E) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      fold (Msg k r) ts (fun y => f (y * S)) = fun x => fold (Mc S) ts f (x * S)
  | [] => rfl
  | t :: ts => by
    funext x
    rw [fold_cons, fold_cons, fold_right S hS f ts, top_apply'', top_apply'']
    congr 1
    exact EZ_right S hS (fold (Mc S) ts f) t.2.1 t.2.2 x

theorem fold_left (A : Mat k r) (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) (f : Mat k r → E) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      fold M ts (fun y => f (A * y)) = fun x => fold M ts f (A * x)
  | [] => rfl
  | t :: ts => by
    funext x
    rw [fold_cons, fold_cons, fold_left A M f ts, top_apply'', top_apply'']
    congr 1
    exact EZ_left A (M t.2.1 t.2.2) (fold M ts f) x

theorem qminor_left {t : ℕ} (A : Mat k r) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E)
    (x : Mat k r) :
    qminorOp (Q.EH k r) a b u (fun y => f (A * y)) x = qminorOp (Q.EH k r) a b u f (A * x) := by
  rw [qm_eq, qm_eq]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [PP]
  rw [fold_left]

theorem qminor_right_all (S : Mat k r) (hS : S ∈ GV k r) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (x : Mat k r) (hx : x * S ∈ GV k r) (hloc : Loc (t : ℕ∞) f (x * S)) :
    qminorOp (Q.EH k r) a b u (fun y => f (y * S)) x =
      ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
        ((∏ j, (S⁻¹) (c j) (a j)) * ∏ j, S (b j) (d j)) • qminorOp (Q.EH k r) c d u f (x * S) := by
  set P := S⁻¹
  set A : (Fin t → Fin (2 * r + k + 1)) → ℂ := fun c => ∏ j, P (c j) (a j) with hA
  set B : (Fin t → Fin (2 * r + k + 1)) → ℂ := fun d => ∏ j, S (b j) (d j) with hB
  have step : ∀ σ : Equiv.Perm (Fin t),
      fold (Mc S) (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) f (x * S) =
        ∑ c, ∑ d, (A c * B d) • PP c d u σ f (x * S) := by
    intro σ
    rw [expandM S hS t _ f (x * S) hx hloc]
    refine (Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ (fun c => ?_)).symm
    simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    congr 1
    · simp only [Function.comp_apply, hA, hB]
      rw [Finset.prod_mul_distrib]
      congr 1
      exact (Equiv.prod_comp σ (fun j => P (c j) (a j))).symm
  rw [qm_eq]
  simp only [PP]
  simp_rw [fold_right S hS f]
  rw [show (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      fold (Mc S) (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) f (x * S)) =
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∑ c, ∑ d, (A c * B d) • PP c d u σ f (x * S) from
    Finset.sum_congr rfl (fun σ _ => by rw [step σ])]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [qm_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal Formalism.FourierDecayAlt.P.FourTermExpansion
  Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Classical in

theorem sum_sortM {M : Type*} [AddCommGroup M] [Module ℂ M] {t N : ℕ} (F : (Fin t → Fin N) → M)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)), F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
      (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C := by
  rw [Formalism.FourierDecayAlt.P.CutMP.CapInv.groupingM (fun i : Fin N => (i : ℕ)) Fin.val_injective F hF hF0 W,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  by_cases h : StrictMono C
  · rw [if_pos h, if_pos (show StrictMono fun l => ((C l : Fin N) : ℕ) from h)]
  · rw [if_neg h, if_neg (show ¬ StrictMono fun l => ((C l : Fin N) : ℕ) from h)]

open Classical in

theorem collapse2 {M : Type*} [AddCommGroup M] [Module ℂ M] {t N : ℕ}
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (A B : (Fin t → Fin N) → ℂ)
    (hr : ∀ c d (τ : Equiv.Perm (Fin t)), D (c ∘ τ) d = ((Equiv.Perm.sign τ : ℤ) : ℂ) • D c d)
    (hr0 : ∀ c d, ¬ Function.Injective c → D c d = 0)
    (hc : ∀ c d (τ : Equiv.Perm (Fin t)), D c (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • D c d)
    (hc0 : ∀ c d, ¬ Function.Injective d → D c d = 0) :
    ∑ c, ∑ d, (A c * B d) • D c d =
      ∑ c ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
        ∑ d ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
          ((∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * A (c ∘ σ)) *
            (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * B (d ∘ σ))) • D c d := by
  set S := Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C)
  set Y : (Fin t → Fin N) → M := fun c =>
    ∑ d ∈ S, (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * B (d ∘ σ)) • D c d with hY
  have inner : ∀ c, ∑ d, (A c * B d) • D c d = A c • Y c := by
    intro c
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, sum_sortM (D c) (hc c) (hc0 c) B]
  simp_rw [inner]
  rw [sum_sortM Y (fun c τ => by simp only [hY, hr, smul_comm _ (((Equiv.Perm.sign τ : ℤ) : ℂ)), Finset.smul_sum])
    (fun c hcn => by simp [hY, hr0 c _ hcn]) A]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [hY, Finset.smul_sum, smul_smul]

theorem det_rows {t N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (c a : Fin t → Fin N) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, P ((c ∘ σ) j) (a j) = (P.submatrix c a).det := by
  rw [Matrix.det_apply']
  rfl

theorem det_cols {t N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (b d : Fin t → Fin N) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, S (b j) ((d ∘ σ) j) = (S.submatrix b d).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open Classical in

theorem qminor_right (S : Mat k r) (hS : S ∈ GV k r) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (x : Mat k r) (hx : x * S ∈ GV k r) (hloc : Loc (t : ℕ∞) f (x * S)) :
    qminorOp (Q.EH k r) a b u (fun y => f (y * S)) x =
      ∑ c ∈ Finset.univ.filter (fun C : Fin t → Fin (2 * r + k + 1) => StrictMono C),
        ∑ d ∈ Finset.univ.filter (fun C : Fin t → Fin (2 * r + k + 1) => StrictMono C),
          ((S⁻¹.submatrix c a).det * (S.submatrix b d).det) • qminorOp (Q.EH k r) c d u f (x * S) := by
  rw [qminor_right_all S hS a b u f x hx hloc]
  rw [collapse2 (fun c d => qminorOp (Q.EH k r) c d u f (x * S)) (fun c => ∏ j, (S⁻¹) (c j) (a j))
    (fun d => ∏ j, S (b j) (d j))
    (fun c d τ => skewRow c d u f (x * S) τ) (fun c d hc => row_zero c d u f (x * S) hc)
    (fun c d τ => skewCol c u f (x * S) hx hloc d τ) (fun c d hd => col_zero c d u f (x * S) hx hloc hd)]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  rw [det_rows, det_cols]

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

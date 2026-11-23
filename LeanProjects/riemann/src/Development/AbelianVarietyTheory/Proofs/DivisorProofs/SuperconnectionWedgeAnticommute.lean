import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DBaseApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeWedgeOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SgnInsertOfNotMemNe
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge GlobalTheory.TorsionForm.Fibrewise
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionForm.WedgeBase

variable {m : ℕ}

def wedgeLin (k : Fin m) : Ext m →ₗ[ℂ] Ext m where
  toFun := wedge k
  map_add' := GlobalTheory.TorsionForm.Pullback.wedge_add k
  map_smul' := GlobalTheory.TorsionForm.Pullback.wedge_smul k

theorem wedge_sum {ι : Type} (k : Fin m) (s : Finset ι) (f : ι → Ext m) :
    wedge k (∑ i ∈ s, f i) = ∑ i ∈ s, wedge k (f i) := map_sum (wedgeLin k) f s

theorem wedge_neg (k : Fin m) (w : Ext m) : wedge k (-w) = -wedge k w := map_neg (wedgeLin k) w

theorem wedge_sub (k : Fin m) (w w' : Ext m) : wedge k (w - w') = wedge k w - wedge k w' :=
  map_sub (wedgeLin k) w w'

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem connForm_wedge (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E) (k : Fin (n + n + g))
    (hk : ∀ a, k ≠ dzb n a) (w : Ext (n + n + g)) :
    connForm τ b v (wedge k w) = wedge k (connForm τ b v w) := by
  unfold connForm
  rw [wedge_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wedge_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [GlobalTheory.TorsionForm.Pullback.wedge_smul, contr_wedge_of_ne (hk a).symm, wedge_neg,
    GlobalTheory.TorsionForm.Pullback.wedge_anticomm (dzb n c) k, neg_neg]

theorem superconn_wedge (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (k : Fin (n + n + g)) (r : Pt E g → Ext (n + n + g)) (P : Pt E g) (hk : ∀ a, k ≠ dzb n a)
    (hr : DifferentiableAt ℝ r P) :
    superconn τ h β u (fun Q => wedge k (r Q)) P = -wedge k (superconn τ h β u r P) := by
  have hL : HasFDerivAt (fun Q => wedge k (r Q))
      ((LinearMap.toContinuousLinearMap (wedgeLin k)).restrictScalars ℝ |>.comp (fderiv ℝ r P)) P :=
    ((LinearMap.toContinuousLinearMap (wedgeLin k)).restrictScalars ℝ).hasFDerivAt.comp P
      hr.hasFDerivAt
  have hfd : ∀ v, fderiv ℝ (fun Q => wedge k (r Q)) P v = wedge k (fderiv ℝ r P v) := fun v => by
    rw [hL.fderiv]; rfl
  have hd10 : ∀ v, d10 (fun Q => wedge k (r Q)) P v = wedge k (d10 r P v) := fun v => by
    rw [d10, d10, hfd, hfd, GlobalTheory.TorsionForm.Pullback.wedge_smul, wedge_sub,
      GlobalTheory.TorsionForm.Pullback.wedge_smul]
  have hd01 : ∀ v, d01 (fun Q => wedge k (r Q)) P v = wedge k (d01 r P v) := fun v => by
    rw [d01, d01, hfd, hfd, GlobalTheory.TorsionForm.Pullback.wedge_smul, GlobalTheory.TorsionForm.Pullback.wedge_add,
      GlobalTheory.TorsionForm.Pullback.wedge_smul]
  have hnab : ∀ v, pointDifference h (fun Q => wedge k (r Q)) P v = wedge k (pointDifference h r P v) := fun v => by
    rw [pointDifference, pointDifference, hd10, GlobalTheory.TorsionForm.Pullback.wedge_add, GlobalTheory.TorsionForm.Pullback.wedge_smul]
  have hN : nablaE τ h β (fun Q => wedge k (r Q)) P = -wedge k (nablaE τ h β r P) := by
    rw [nablaE, nablaE, wedge_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnab, hd01, connForm_wedge τ _ _ k hk, ← GlobalTheory.TorsionForm.Pullback.wedge_add,
      GlobalTheory.TorsionForm.Pullback.wedge_anticomm (dt g i) k,
      GlobalTheory.TorsionForm.Pullback.wedge_anticomm (dtb g i) k, ← neg_add, ← GlobalTheory.TorsionForm.Pullback.wedge_add]
  have hV : dbarV (fun Q => wedge k (r Q)) P = -wedge k (dbarV r P) := by
    rw [dbarV, dbarV, wedge_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hd01, GlobalTheory.TorsionForm.Pullback.wedge_anticomm (dzb n a) k]
  have hA : dbarAdj τ h (fun Q => wedge k (r Q)) P = -wedge k (dbarAdj τ h r P) := by
    rw [dbarAdj, dbarAdj, wedge_neg, wedge_sum, neg_neg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [wedge_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hnab, contr_wedge_of_ne (hk c).symm, GlobalTheory.TorsionForm.Pullback.wedge_smul, smul_neg, neg_neg]
  rw [superconn, superconn, hN, hV, hA, GlobalTheory.TorsionForm.Pullback.wedge_add,
    GlobalTheory.TorsionForm.Pullback.wedge_smul, GlobalTheory.TorsionForm.Pullback.wedge_add, ← neg_add, smul_neg, neg_add]

end GlobalTheory.TorsionForm.WedgeBase

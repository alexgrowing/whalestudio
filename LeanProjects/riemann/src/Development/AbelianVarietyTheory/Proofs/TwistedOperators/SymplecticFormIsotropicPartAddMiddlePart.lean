import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerForm

variable {D : D7}

local infixl:70 " ⬝ " => HMul.hMul

def ad {m n : ℕ} (A : Mx D m n) : Mx D n m := Formalism.UG.cT (cA D) A

theorem ad_mul {l m n : ℕ} (A : Mx D l m) (B : Mx D m n) :
    ad (HMul.hMul A B : Mx D l n) = HMul.hMul (ad B) (ad A) := by
  unfold ad Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cA_incA_sig (e : D.host.E) : cA D (incA D e) = incA D (D.sp.cm.sig e) := by
  simp only [cA, sigR, incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

theorem ad_map {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    ad (A.map (incA D) : Mx D m n) = (adj D A).map (incA D) := by
  unfold ad adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, cA_incA_sig]
  rfl

theorem adj_mul {l m n : ℕ} (A : Matrix (Fin l) (Fin m) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  unfold adj Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_adj {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D (adj D A) = A := by
  unfold adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact star_star (A i j)

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  unfold adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact GlobalTheory.LatVac.gram_star V j i

theorem adj_gram_inv (V : HSp D) : adj D V.gram⁻¹ = V.gram⁻¹ := by
  have hu := GlobalTheory.LatVac.gram_det_isUnit V
  symm
  apply Matrix.inv_eq_left_inv
  calc adj D V.gram⁻¹ * V.gram = adj D V.gram⁻¹ * adj D V.gram := by rw [adj_gram]
    _ = adj D (V.gram * V.gram⁻¹) := (adj_mul _ _).symm
    _ = 1 := by
      rw [Matrix.mul_nonsing_inv (h := hu)]
      unfold adj Formalism.UG.cT
      simp

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹.map (incA D) * ad y) * T.gram.map (incA D) * x) := by
  unfold hO
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ad, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_mul_mul (V W : HSp D) {m n : ℕ} (y₁ : Mx D W.rank m) (y₂ : Mx D W.rank n)
    (P₁ : Matrix (Fin m) (Fin V.rank) D.host.E) (P₂ : Matrix (Fin n) (Fin V.rank) D.host.E) :
    hO V W (HMul.hMul y₁ (P₁.map (incA D))) (HMul.hMul y₂ (P₂.map (incA D))) =
      Matrix.trace (ad y₂ ⬝ W.gram.map (incA D) ⬝ y₁ ⬝ (P₁ * V.gram⁻¹ * adj D P₂).map (incA D)) := by
  rw [hO_eq_trace, ad_mul, ad_map, Matrix.map_mul, Matrix.map_mul]
  have key := Matrix.trace_mul_comm (V.gram⁻¹.map (incA D) * (adj D P₂).map (incA D))
    (ad y₂ * W.gram.map (incA D) * y₁ * P₁.map (incA D))
  simpa only [Matrix.mul_assoc] using key

theorem adj_zero {m n : ℕ} : adj D (0 : Matrix (Fin m) (Fin n) D.host.E) = 0 := by
  unfold adj Formalism.UG.cT
  simp

theorem gram_sandwich (V : HSp D) {m n : ℕ} (A : Matrix (Fin m) (Fin V.rank) D.host.E)
    (B' : Matrix (Fin V.rank) (Fin n) D.host.E) : A * V.gram * V.gram⁻¹ * (V.gram * B') = A * V.gram * B' := by
  rw [Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V), Matrix.mul_assoc]

section Split

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}

theorem coef_iso_iso (hs : IsIsoSplit V V' C B) :
    adj D C * V.gram * V.gram⁻¹ * adj D (adj D C * V.gram) = 0 := by
  have hC : adj D C * V.gram * C = 0 := hs.frame.2.2
  rw [adj_mul, adj_adj, adj_gram, Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V),
    ← Matrix.mul_assoc]
  exact hC

theorem coef_iso_mid (hs : IsIsoSplit V V' C B) :
    adj D C * V.gram * V.gram⁻¹ * adj D (V'.gram⁻¹ * adj D B * V.gram) = 0 := by
  rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_gram_inv,
    Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V), ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hs.orth, Matrix.zero_mul]

theorem coef_mid_iso (hs : IsIsoSplit V V' C B) :
    V'.gram⁻¹ * adj D B * V.gram * V.gram⁻¹ * adj D (adj D C * V.gram) = 0 := by
  have hBC : adj D B * (V.gram * C) = 0 := by
    have h := congrArg (adj D) hs.orth
    rwa [adj_mul, adj_mul, adj_adj, adj_gram, adj_zero] at h
  rw [adj_mul, adj_adj, adj_gram, Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V),
    Matrix.mul_assoc, hBC, Matrix.mul_zero]

theorem coef_mid_mid (hs : IsIsoSplit V V' C B) :
    V'.gram⁻¹ * adj D B * V.gram * V.gram⁻¹ * adj D (V'.gram⁻¹ * adj D B * V.gram) = V'.gram⁻¹ := by
  rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_gram_inv,
    Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (adj D B), ← Matrix.mul_assoc (adj D B * V.gram), hs.isom,
    Matrix.mul_nonsing_inv (h := GlobalTheory.LatVac.gram_det_isUnit V'), Matrix.mul_one]

theorem trace_swap {m n : ℕ} (Z : Mx D m m) (A : Mx D m n) (Y : Mx D n n) (X : Mx D n m) :
    Matrix.trace (Z ⬝ A ⬝ Y ⬝ X) = Matrix.trace (A ⬝ Y ⬝ X ⬝ Z) := by
  have key := Matrix.trace_mul_comm Z (A * Y * X)
  simpa only [Matrix.mul_assoc] using key

theorem hO_isoPart_add_midPart (hs : IsIsoSplit V V' C B) (y y' : Mx D W.rank r) (x x' : WO V' W) :
    hO V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = hO V' W x x' := by
  rw [hO_add_left, hO_add_right, hO_add_right]
  unfold isoPart midPart
  rw [hO_mul_mul, hO_mul_mul, hO_mul_mul, hO_mul_mul, coef_iso_iso hs, coef_iso_mid hs, coef_mid_iso hs,
    coef_mid_mid hs]
  simp only [Matrix.map_zero, map_zero, Matrix.mul_zero, Matrix.trace_zero, zero_add]
  rw [hO_eq_trace, trace_swap]

end Split

theorem symplOH_isoPart_add_midPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (y y' : Mx D W.rank r) (x x' : WO V' W),
    symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x' := by
  intro D V V' W r C B hs y y' x x'
  unfold symplOH symplO
  rw [hO_isoPart_add_midPart hs]

end GlobalTheory.TowerForm

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.TransvDec

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

def colM {n : ℕ} (a : Fin n → AE D) : Mx D n 1 := replicateCol (Fin 1) a

theorem colM_mulVec {m n : ℕ} (M : Mx D m n) (a : Fin n → AE D) : colM (M *ᵥ a) = M ⬝ colM a :=
  replicateCol_mulVec M a

theorem colM_mul {n : ℕ} (a : Fin n → AE D) (K : Mx D 1 1) : colM a ⬝ K = colM (K 0 0 • a) := by
  ext i j
  rw [Subsingleton.elim j 0]
  simp [colM, Matrix.mul_apply, mul_comm]

theorem form_eq (S : HSp D) (y v : VA S) : form S y v = (adj (colM v) ⬝ (gA S ⬝ colM y)) 0 0 := by
  rw [← colM_mulVec]; rfl

theorem ext_colM {m n : ℕ} {M N : Mx D m n} (h : ∀ y : Fin n → AE D, M ⬝ colM y = N ⬝ colM y) : M = N := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have := h (Pi.single i 1)
  rw [← colM_mulVec, ← colM_mulVec] at this
  exact funext fun k => congrFun (congrFun this k) 0

theorem mt_transv {S : HSp D} {w v : VA S} {u : GA D S} (hu : IsTransv S w v u) :
    mt S u = 1 + colM w ⬝ (adj (colM v) ⬝ gA S) - colM v ⬝ (adj (colM w) ⬝ gA S) -
      half D • (colM w ⬝ (adj (colM v) ⬝ (gA S ⬝ (colM v ⬝ (adj (colM w) ⬝ gA S))))) := by
  refine ext_colM fun y => ?_
  have h : mt S u *ᵥ y = transv S w v y := hu y
  rw [← colM_mulVec, h]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc]
  have e : (adj (colM v) ⬝ (gA S ⬝ (colM v ⬝ (adj (colM w) ⬝ (gA S ⬝ colM y))))) 0 0 = form S v v * form S y w := by
    rw [form_eq, form_eq, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (colM v)), Matrix.mul_apply,
      Fin.sum_univ_one]
  rw [colM_mul w, colM_mul w, e, colM_mul v, ← form_eq, ← form_eq]
  ext i j
  simp [colM, transv, mul_assoc]

def unip {ρ : ℕ} (A γ : Mx D ρ 1) (h : adj γ ⬝ A = 0) : GL (Fin ρ) (AE D) where
  val := 1 + A ⬝ adj γ
  inv := 1 - A ⬝ adj γ
  val_inv := by
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, cancel₂ h,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, add_sub_cancel_right]
  inv_val := by
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, cancel₂ h,
      Matrix.zero_mul, Matrix.mul_zero, sub_zero, sub_add_cancel]

theorem val_unip {ρ : ℕ} (A γ : Mx D ρ 1) (h : adj γ ⬝ A = 0) : (unip A γ h).1 = 1 + A ⬝ adj γ := rfl

theorem val_unip_inv {ρ : ℕ} (A γ : Mx D ρ 1) (h : adj γ ⬝ A = 0) : ((unip A γ h)⁻¹).1 = 1 - A ⬝ adj γ := rfl

theorem det_eq_one_of_val {R : Type} [CommRing R] {m n : ℕ} (g : GL (Fin m) R) (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) (hg : g.1 = 1 + A * B) (h : B * A = 0) : Matrix.GeneralLinearGroup.det g = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, hg, Matrix.det_one_add_mul_comm, h, add_zero, det_one, Units.val_one]

theorem det_unip {ρ : ℕ} (A γ : Mx D ρ 1) (h : adj γ ⬝ A = 0) : Matrix.GeneralLinearGroup.det (unip A γ h :) = 1 := by
  have hg := val_unip A γ h
  generalize unip A γ h = g at hg ⊢
  exact det_eq_one_of_val (R := AE D) g A (adj γ) hg h

def skewPart {ρ : ℕ} (A α γ : Mx D ρ 1) : skewA D ρ :=
  ⟨A ⬝ adj α - α ⬝ adj A + (half D • (A ⬝ (adj γ ⬝ (α ⬝ adj A))) - half D • (A ⬝ (adj α ⬝ (γ ⬝ adj A)))), by
    simp only [mem_skewA, adj_add, adj_sub, adj_smul, adj_mul, adj_adj, cA_half, Matrix.mul_assoc]
    abel⟩

theorem qS_skewPart {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (A α γ : Mx D ρ 1) (T : HSp D) (x : Mx D T.rank ρ)
    (hx : x ⬝ A = 0) : d.qS T (skewPart A α γ) x = 0 := by
  have h : x ⬝ (skewPart A α γ).1 = -(x ⬝ α ⬝ adj A) := by
    simp only [skewPart, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, cancel₂ hx, Matrix.zero_mul, smul_zero,
      sub_zero, add_zero, zero_sub, Matrix.mul_assoc]
  rw [HypDec.qS, HypDec.symplOH_extX_extY, h, pairS, adj_neg, adj_mul, adj_adj, Matrix.neg_mul, trace_neg,
    Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hx, Matrix.mul_zero, Matrix.mul_zero,
    trace_zero, neg_zero, map_zero]

section Main

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {A α γ : Mx D ρ 1} {β : Mx D S₀.rank 1} (h : adj γ ⬝ A = 0)

theorem prod_jX (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    mt S (d.levi (unip A γ h) * d.nB b * d.nC c) ⬝ d.jX = d.jX + d.jX ⬝ (A ⬝ adj γ) := by
  rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX, val_unip, Matrix.mul_add,
    Matrix.mul_one]

theorem wittCoreColumns_transvectionLeviProduct (s : Mx D 1 S₀.rank) (c : skewA D ρ) :
    mt S (d.levi (unip A γ h) * d.nB (A ⬝ s) * d.nC c) ⬝ d.j0 = d.j0 + d.jX ⬝ (A ⬝ s) := by
  rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic,
    cancel₂ (d.levi_jX _), val_unip, Matrix.mul_assoc, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, cancel₂ h,
    Matrix.zero_mul, Matrix.mul_zero, add_zero]

set_option maxHeartbeats 1000000 in
theorem prod_jY :
    mt S (d.levi (unip A γ h) * d.nB (A ⬝ (adj β ⬝ gA S₀)) * d.nC (skewPart A α γ)) ⬝ d.jY =
      d.jY + d.jX ⬝ (A ⬝ adj α) - (d.jX ⬝ α + d.j0 ⬝ β + d.jY ⬝ γ) ⬝ adj A -
        half D • (d.jX ⬝ (A ⬝ ((adj γ ⬝ α + adj β ⬝ (gA S₀ ⬝ β) + adj α ⬝ γ) ⬝ adj A))) := by
  have hp : plus S₀ (A ⬝ (adj β ⬝ gA S₀)) = β ⬝ adj A := by
    simp only [plus, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, giA_gA_cancel]
  have hh := half_smul_add (d.jX ⬝ (A ⬝ (adj γ ⬝ (α ⬝ adj A))))
  have hm := val_unip A γ h
  have hm' := val_unip_inv A γ h
  generalize unip A γ h = g at hm hm' ⊢
  simp only [mt_mul, Matrix.mul_assoc, d.nC_jY, Matrix.mul_add, d.nB_jY, cancel₂ (d.nB_jX _), hp,
    Matrix.mul_sub, d.levi_jY, cancel₂ (d.wittDecomp_levi_inclAnisotropic _), cancel₂ (d.levi_jX _)]
  rw [hm, hm']
  simp only [skewPart, adj_sub, adj_mul, adj_adj, adj_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.mul_smul, smul_add, smul_zero, Matrix.mul_assoc, cancel₂ h,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, sub_zero, zero_add]
  generalize half D • (d.jX ⬝ (A ⬝ (adj γ ⬝ (α ⬝ adj A)))) = t at hh ⊢
  rw [← hh]
  abel

end Main

set_option maxHeartbeats 1000000 in

theorem eq_levi_nB_nC {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (A : Mx D ρ 1) (V : Mx D S.rank 1)
    (h : adj (d.pY ⬝ V) ⬝ A = 0) (u : GA D S)
    (hu : mt S u = 1 + d.jX ⬝ A ⬝ (adj V ⬝ gA S) - V ⬝ (adj (d.jX ⬝ A) ⬝ gA S) -
      half D • (d.jX ⬝ A ⬝ (adj V ⬝ (gA S ⬝ (V ⬝ (adj (d.jX ⬝ A) ⬝ gA S)))))) :
    u = d.levi (unip A (d.pY ⬝ V) h) * d.nB (A ⬝ (adj (d.p0 ⬝ V) ⬝ gA S₀)) *
      d.nC (skewPart A (d.pX ⬝ V) (d.pY ⬝ V)) := by
  have hV : d.jX ⬝ (d.pX ⬝ V) + d.j0 ⬝ (d.p0 ⬝ V) + d.jY ⬝ (d.pY ⬝ V) = V := by
    simp only [← Matrix.mul_assoc]
    rw [← Matrix.add_mul, ← Matrix.add_mul, d.sum_eq_one, Matrix.one_mul]
  have hX : adj V ⬝ (gA S ⬝ d.jX) = adj (d.pY ⬝ V) := by
    rw [d.pY_eq, adj_mul, adj_mul, adj_adj, adj_gA]
  have hY : adj V ⬝ (gA S ⬝ d.jY) = adj (d.pX ⬝ V) := by
    rw [d.pX_eq, adj_mul, adj_mul, adj_adj, adj_gA]
  have h0 : adj V ⬝ (gA S ⬝ d.j0) = adj (d.p0 ⬝ V) ⬝ gA S₀ := by
    simp only [d.p0_eq, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one]
  have hK : adj (d.pY ⬝ V) ⬝ (d.pX ⬝ V) + adj (d.p0 ⬝ V) ⬝ (gA S₀ ⬝ (d.p0 ⬝ V)) + adj (d.pX ⬝ V) ⬝ (d.pY ⬝ V) =
      adj V ⬝ (gA S ⬝ V) := by
    rw [← cancel₃ hX, ← cancel₃ hY, ← Matrix.mul_assoc (adj (d.p0 ⬝ V)), ← cancel₃ h0, ← Matrix.mul_add,
      ← Matrix.mul_add, ← Matrix.mul_add, ← Matrix.mul_add, hV]
  have hP : adj (d.jX ⬝ A) ⬝ gA S = adj A ⬝ d.pY := by rw [d.pY_eq, adj_mul, Matrix.mul_assoc]
  simp only [hP] at hu
  refine d.ga_ext ?_ ?_ ?_
  · rw [prod_jX, hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, d.pY_jX, hX,
      Matrix.mul_zero, Matrix.one_mul, smul_zero, sub_zero]
  · rw [wittCoreColumns_transvectionLeviProduct, hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, d.pY_j0, h0,
      Matrix.mul_zero, Matrix.one_mul, smul_zero, sub_zero]
  · rw [prod_jY, hV, hK, hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, d.pY_jY, hY, Matrix.one_mul,
      Matrix.mul_one]

end GlobalTheory.Unf.TransvDec

namespace GlobalTheory.Unf

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction TransvDec

theorem transv_eq_levi_nB_nC : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA S), GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d a) v = 0 → ∀ u : GA D S, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv S (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d a) v u → ∃ (m : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ), u = d.levi m * d.nB b * d.nC c ∧ Matrix.GeneralLinearGroup.det m = 1 ∧ ∀ (T : HSp D) (x : Mx D T.rank ρ), x *ᵥ a = 0 → x ⬝ m.1 = x ∧ x ⬝ b = 0 ∧ d.qS T c x = 0 := by
  intro D S S₀ ρ d a v hv u hu
  have hw : colM (vecX d a) = d.jX ⬝ colM a := colM_mulVec _ _
  have h : adj (d.pY ⬝ colM v) ⬝ colM a = 0 := by
    rw [form_eq, hw] at hv
    rw [d.pY_eq, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, Matrix.mul_assoc]
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact hv
  have hm := mt_transv hu
  rw [hw] at hm
  refine ⟨_, _, _, eq_levi_nB_nC d (colM a) (colM v) h u hm, det_unip _ _ h, fun T x hx => ?_⟩
  have hx' : x ⬝ colM a = 0 := by
    rw [← colM_mulVec, hx]; rfl
  refine ⟨?_, ?_, qS_skewPart d _ _ _ T x hx'⟩
  · change x ⬝ (1 + colM a ⬝ adj (d.pY ⬝ colM v)) = x
    rw [Matrix.mul_add, Matrix.mul_one, cancel₂ hx', Matrix.zero_mul, add_zero]
  · rw [cancel₂ hx', Matrix.zero_mul]

end GlobalTheory.Unf

end

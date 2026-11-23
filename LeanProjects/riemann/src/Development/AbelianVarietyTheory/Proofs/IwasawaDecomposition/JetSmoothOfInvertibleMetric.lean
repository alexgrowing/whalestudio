import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply

set_option autoImplicit false

noncomputable section

open Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.ChernReg

section General

variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem contDiffOn_del_apply {f : E → F} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) {p v : W → E} {t : Set W}
    (hp : ContDiffOn ℝ ∞ p t) (hv : ContDiffOn ℝ ∞ v t) (hps : Set.MapsTo p t s) :
    ContDiffOn ℝ ∞ (fun x => GlobalTheory.del f (p x) (v x)) t := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
  have hc : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f (p x)) t := hd.comp hp hps
  simp only [GlobalTheory.del_apply]
  exact ((hc.clm_apply hv).sub ((hc.clm_apply (hv.const_smul Complex.I)).const_smul Complex.I)).const_smul _

end General

section Matrix

variable {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype ι] [DecidableEq ι]

theorem contDiffOn_det {M : W → Matrix ι ι ℂ} {t : Set W} (hM : ∀ k l, ContDiffOn ℝ ∞ (fun x => M x k l) t) :
    ContDiffOn ℝ ∞ (fun x => (M x).det) t := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hM _ _)

theorem contDiffOn_inv_apply {M : W → Matrix ι ι ℂ} {t : Set W} (hM : ∀ k l, ContDiffOn ℝ ∞ (fun x => M x k l) t)
    (hu : ∀ x ∈ t, IsUnit (M x).det) (k l : ι) : ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ k l) t := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((contDiffOn_det hM).inv fun x hx => (hu x hx).ne_zero).mul (contDiffOn_det fun i j => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hM _ _

end Matrix

variable {d : ℕ} {U : Set (V d)} {b : V d → Matrix (Fin d) (Fin d) ℂ}

theorem contDiffOn_chris (hU : IsOpen U) (hb : ∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U)
    (hu : ∀ v ∈ U, IsUnit (b v).det) :
    ContDiffOn ℝ ∞ (fun q : V d × V d => christoffel b q.1 q.2) (U ×ˢ (Set.univ : Set (V d))) := by
  have hfst : Set.MapsTo (Prod.fst : V d × V d → V d) (U ×ˢ (Set.univ : Set (V d))) U := fun q hq => hq.1
  have hinv : ∀ k l, ContDiffOn ℝ ∞ (fun q : V d × V d => (b q.1)⁻¹ k l) (U ×ˢ (Set.univ : Set (V d))) := fun k l =>
    contDiffOn_inv_apply (fun i j => (hb i j).comp contDiffOn_fst hfst) (fun q hq => hu _ hq.1) k l
  have hdel : ∀ k l, ContDiffOn ℝ ∞ (fun q : V d × V d => GlobalTheory.del (fun v => b v k l) q.1 q.2)
      (U ×ˢ (Set.univ : Set (V d))) := fun k l =>
    contDiffOn_del_apply hU (hb k l) contDiffOn_fst contDiffOn_snd hfst
  have hξ : ∀ k, ContDiffOn ℝ ∞ (fun q : V d × V d => q.2.ofLp k) (U ×ˢ (Set.univ : Set (V d))) := fun k =>
    ((EuclideanSpace.proj k : V d →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn contDiffOn_snd
  rw [← (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).comp_contDiffOn_iff]
  refine contDiffOn_pi.2 fun i => ?_
  simp only [Function.comp_def, PiLp.continuousLinearEquiv_apply, christoffel, WithLp.ofLp_toLp, Matrix.vecMul, dotProduct, Matrix.of_apply]
  exact ContDiffOn.sum fun j _ => (ContDiffOn.sum fun k _ => (hξ k).mul (hdel k j)).mul (hinv j i)

theorem contDiffOn_jet (d : ℕ) (U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (b : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ)
    (hU : IsOpen U) (hb : ∀ k l, ContDiffOn ℝ ∞ (fun v => b v k l) U) (hu : ∀ v ∈ U, IsUnit (b v).det) (n : ℕ) :
    ContDiffOn ℝ ∞ (GlobalTheory.ChernReg.jet b n) (U ×ˢ (Set.univ : Set (ReciprocityTheory.L2DbarEstimates.V d))) := by
  induction n with
  | zero => exact contDiffOn_fst
  | succ n ih =>
    rw [show jet b (n + 1) = fun q => GlobalTheory.del (jet b n) (id q) (q.2, -christoffel b q.1 q.2) from funext (jet_succ b n)]
    exact contDiffOn_del_apply (hU.prod isOpen_univ) ih contDiffOn_id
      (contDiffOn_snd.prodMk (contDiffOn_chris hU hb hu).neg) (Set.mapsTo_id _)

end GlobalTheory.ChernReg

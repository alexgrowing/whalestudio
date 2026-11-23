import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CruxSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDet
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulConjTransposeEq

noncomputable section

open Matrix Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem analyticAt_entryM {ι κ : Type} [Fintype ι] [Fintype κ] (i : ι) (j : κ) (x0 : Matrix ι κ ℂ) :
    AnalyticAt ℂ (fun x : Matrix ι κ ℂ => x i j) x0 := by
  let L : Matrix ι κ ℂ →ₗ[ℂ] ℂ := { toFun := fun x => x i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).analyticAt x0

theorem analyticAt_matrix {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι κ : Type} [Fintype ι] [Fintype κ]
    {F : E → Matrix ι κ ℂ} {x0 : E} (h : ∀ i j, AnalyticAt ℂ (fun x => F x i j) x0) : AnalyticAt ℂ F x0 := by
  exact (analyticAt_pi_iff (f := fun i x => F x i)).mpr fun i =>
    (analyticAt_pi_iff (f := fun j x => F x i j)).mpr fun j => h i j

theorem analyticAt_det_comp {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : E → Matrix ι ι ℂ} {x0 : E} (h : AnalyticAt ℂ F x0) : AnalyticAt ℂ (fun x => (F x).det) x0 := by
  have he : ∀ i j, AnalyticAt ℂ (fun x => F x i j) x0 := fun i j =>
    (analyticAt_entryM i j (F x0)).comp h
  have hs := Finset.analyticAt_sum (c := x0) (Finset.univ : Finset (Equiv.Perm ι))
    (f := fun σ x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, F x (σ i) i)
    (fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i))
  have hfun : (fun x => (F x).det) =
      ∑ σ : Equiv.Perm ι, fun x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, F x (σ i) i := by
    funext x
    simp [Matrix.det_apply', Finset.sum_apply]
  rw [hfun]
  exact hs

theorem analyticAt_inv_entry (x0 : M2 n) (h : x0.det ≠ 0) (i j : Fin n ⊕ Fin n) :
    AnalyticAt ℂ (fun x : M2 n => x⁻¹ i j) x0 := by
  have hadj : AnalyticAt ℂ (fun x : M2 n => x.adjugate i j) x0 := by
    simp only [Matrix.adjugate_apply]
    apply analyticAt_det_comp
    apply analyticAt_matrix
    intro a b
    by_cases ha : a = j
    · subst ha
      simp only [Matrix.updateRow_self]
      exact analyticAt_const
    · simp only [Matrix.updateRow_ne ha]
      exact analyticAt_entryM a b x0
  have hdet : AnalyticAt ℂ (fun x : M2 n => x.det) x0 :=
    analyticAt_det_comp (F := fun x : M2 n => x) analyticAt_id
  have h2 := (hdet.inv h).mul hadj
  have hfun : (fun x : M2 n => x⁻¹ i j) =
      (fun x : M2 n => x.det)⁻¹ * fun x : M2 n => x.adjugate i j := by
    funext x
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [hfun]
  exact h2

theorem analyticAt_first_cayley_block (x0 : M2 n) : AnalyticAt ℂ (fun x : M2 n => u1 x) x0 := by
  refine analyticAt_matrix fun a b => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact (analyticAt_const.mul (analyticAt_entryM _ _ x0)).add (analyticAt_entryM _ _ x0)

theorem analyticAt_inverse_first_block (x0 : M2 n) (h : x0.det ≠ 0) : AnalyticAt ℂ (fun x : M2 n => ub1 x) x0 := by
  refine analyticAt_matrix fun a b => ?_
  simp only [ub1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.of_apply, smul_eq_mul]
  exact (analyticAt_inv_entry x0 h _ _).add (analyticAt_const.mul (analyticAt_inv_entry x0 h _ _))

theorem continuousOn_pf : ContinuousOn (fun x : M2 n => (u1 x).det * (ub1 x).det) (Dom n) := by
  intro x hx
  have hd : x.det ≠ 0 := hx.1.ne_zero
  exact ((analyticAt_det_comp (analyticAt_first_cayley_block x)).mul (analyticAt_det_comp (analyticAt_inverse_first_block x hd))).continuousAt.continuousWithinAt

theorem isOpen_domZ : IsOpen (DomZ n) := by
  exact continuousOn_pf.isOpen_inter_preimage isOpen_dom Complex.isOpen_slitPlane

theorem gset_sub_domZ : GSet n ⊆ DomZ n := by
  intro g hg
  have hG : InG g := hg
  have hu : (u1 g).det ≠ 0 := det_first_cayley_block_ne_zero hG
  have hub : ub1 g = (u1 g)ᴴ := inverse_first_block_eq_of_group hG
  have hp : (u1 g).det * (ub1 g).det = ((Complex.normSq (u1 g).det : ℝ) : ℂ) := by
    rw [hub, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj]
  show (IsUnit (det g) ∧ (u1 g).det ≠ 0 ∧ (u2 g).det ≠ 0 ∧ (ub1 g).det ≠ 0) ∧
    (u1 g).det * (ub1 g).det ∈ Complex.slitPlane
  refine ⟨⟨isUnit_det_of_inG hG, hu, det_second_cayley_block_ne_zero hG, ?_⟩, ?_⟩
  · rw [hub, Matrix.det_conjTranspose]
    exact star_ne_zero.mpr hu
  · rw [hp, Complex.ofReal_mem_slitPlane]
    exact Complex.normSq_pos.mpr hu

theorem fzHol : FzHol := by
  intro n m e
  refine ⟨isOpen_domZ, gset_sub_domZ, ?_⟩
  rintro ⟨z, x⟩ ⟨-, hx⟩
  have hx' : (IsUnit (det x) ∧ (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0 ∧ (ub1 x).det ≠ 0) ∧
      (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := hx
  have hdet : x.det ≠ 0 := hx'.1.1.ne_zero
  have hsn : AnalyticAt ℂ (Prod.snd : ℂ × M2 n → M2 n) (z, x) := analyticAt_snd
  have hu1' := AnalyticAt.comp (g := fun y : M2 n => u1 y) (analyticAt_first_cayley_block x) hsn
  have hub1' := AnalyticAt.comp (g := fun y : M2 n => ub1 y) (analyticAt_inverse_first_block x hdet) hsn
  have hu1 : AnalyticAt ℂ (fun q : ℂ × M2 n => u1 q.2) (z, x) := hu1'
  have hub1 : AnalyticAt ℂ (fun q : ℂ × M2 n => ub1 q.2) (z, x) := hub1'
  have hD : AnalyticAt ℂ (fun q : ℂ × M2 n => q.2.det) (z, x) :=
    analyticAt_det_comp (F := fun q : ℂ × M2 n => q.2) hsn
  have hU : AnalyticAt ℂ (fun q : ℂ × M2 n => (u1 q.2).det) (z, x) := analyticAt_det_comp hu1
  have hUb : AnalyticAt ℂ (fun q : ℂ × M2 n => (ub1 q.2).det) (z, x) := analyticAt_det_comp hub1
  have h1 : AnalyticAt ℂ (fun q : ℂ × M2 n => q.2.det ^ e) (z, x) := hD.zpow hdet
  have h2 : AnalyticAt ℂ (fun q : ℂ × M2 n => (u1 q.2).det ^ (-(m : ℤ))) (z, x) :=
    hU.zpow hx'.1.2.1
  have h3 : AnalyticAt ℂ
      (fun q : ℂ × M2 n => ((u1 q.2).det * (ub1 q.2).det) ^ (-q.1)) (z, x) :=
    (hU.mul hUb).cpow analyticAt_fst.neg hx'.2
  exact (h1.mul h2).mul h3

end PositivityTheory.Rg.Sw.HSt

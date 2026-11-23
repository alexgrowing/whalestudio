import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.Expand

variable {n : ℕ}

def co (q : Idx n) (M : Mat n) : ℝ := if q.1 then (M q.2.1 q.2.2).re else (M q.2.1 q.2.2).im

theorem sum_single_ite (a b : Fin n) (g : Fin n → Fin n → ℂ) :
    ∑ x, ∑ i, (if x = a ∧ i = b then g x i else 0) = g a b := by
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp),
    Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem sum_co_smul (M : Mat n) : ∑ q : Idx n, co q M • bs q = M := by
  ext a b
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, co, bs, Matrix.sum_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.single_apply, if_true, Bool.false_eq_true, if_false, smul_ite,
    smul_zero]
  rw [sum_single_ite a b (fun x i => (M x i).re • (1 : ℂ)),
    sum_single_ite a b (fun x i => (M x i).im • Complex.I)]
  simp [Complex.ext_iff]

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y i j) :=
  contDiff_apply_apply ℝ ℂ i j

theorem contDiff_det (F : Mat n → Mat n) (h : ∀ i j, ContDiff ℝ ∞ (fun y => F y i j)) :
    ContDiff ℝ ∞ (fun y => (F y).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_adjugate (i k : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y.adjugate i k) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det (fun y => y.updateRow k (Pi.single i 1)) fun a b => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry a b

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne.preimage (contDiff_det (n := n) id contDiff_entry).continuous

theorem contDiffOn_inv_entry (i k : Fin n) :
    ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹ i k) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹ * y.adjugate i k) (GLs n) :=
    ((contDiff_det (n := n) id contDiff_entry).contDiffOn.inv fun y hy => hy).mul
      (contDiff_adjugate i k).contDiffOn
  refine h.congr fun y _ => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]

theorem co_smooth (p q : Idx n) :
    ContDiffOn ℝ ∞ (fun y : Mat n => co q (y⁻¹ * bs p)) (GLs n) := by
  have he : ∀ a b, ContDiffOn ℝ ∞ (fun y : Mat n => (y⁻¹ * bs p) a b) (GLs n) := by
    intro a b
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun k _ => (contDiffOn_inv_entry a k).mul contDiffOn_const
  rcases q with ⟨_ | _, a, b⟩
  · simpa [co, Function.comp_def] using Complex.imCLM.contDiff.comp_contDiffOn (he a b)
  · simpa [co, Function.comp_def] using Complex.reCLM.contDiff.comp_contDiffOn (he a b)

theorem contDiff_mul_right (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (contDiff_entry a k).mul contDiff_const

theorem Rw_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Idx n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    exact (ih.fderiv_of_isOpen isOpen_GLs (by simp)).clm_apply
      (contDiff_mul_right (bs p)).contDiffOn

theorem fderiv_mul_expand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Mat n → V)
    (y M : Mat n) : fderiv ℝ H y (y * M) = ∑ q, co q M • Rd (bs q) H y := by
  conv_lhs => rw [← sum_co_smul M]
  rw [Matrix.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mul_smul, map_smul]
  rfl

theorem fderiv_expand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Mat n → V)
    {y : Mat n} (hy : y ∈ GLs n) (X : Mat n) :
    fderiv ℝ H y X = ∑ q, co q (y⁻¹ * X) • Rd (bs q) H y := by
  have hu : IsUnit y.det := isUnit_iff_ne_zero.2 hy
  rw [← fderiv_mul_expand, Matrix.mul_nonsing_inv_cancel_left y X hu]

theorem exists_integralCombination_of_mem_completedLattice (L : List (Idx n)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → Mat n → ℝ) (w : ι → List (Idx n)),
      (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
        ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  induction L with
  | nil =>
    exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => [], fun _ => contDiffOn_const,
      fun V _ _ f _ y _ => by simp [Dw_nil, Rw]⟩
  | cons p L ih =>
    obtain ⟨ι, _, c, w, hc, h⟩ := ih
    refine ⟨ι ⊕ (ι × Idx n), inferInstance,
      Sum.elim (fun i y => fderiv ℝ (c i) y (bs p)) (fun e y => c e.1 y * co e.2 (y⁻¹ * bs p)),
      Sum.elim w (fun e => e.2 :: w e.1), ?_, ?_⟩
    · rintro (i | ⟨i, q⟩)
      · exact ((hc i).fderiv_of_isOpen isOpen_GLs (by simp)).clm_apply contDiffOn_const
      · exact (hc i).mul (co_smooth p q)
    · intro V _ _ f hf y hy
      have hev : Dw L f =ᶠ[nhds y] fun z => ∑ i, c i z • Rw (w i) f z := by
        filter_upwards [isOpen_GLs.mem_nhds hy] with z hz using h V f hf z hz
      have hdc : ∀ i, DifferentiableAt ℝ (c i) y := fun i =>
        ((hc i).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
      have hdr : ∀ i, DifferentiableAt ℝ (Rw (w i) f) y := fun i =>
        ((Rw_smooth hf (w i)).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
      show fderiv ℝ (Dw L f) y (bs p) = _
      have hd : HasFDerivAt (fun z => ∑ i, c i z • Rw (w i) f z)
          (∑ i, (c i y • fderiv ℝ (Rw (w i) f) y +
            (fderiv ℝ (c i) y).smulRight (Rw (w i) f y))) y :=
        HasFDerivAt.fun_sum fun i _ => (hdc i).hasFDerivAt.fun_smul (hdr i).hasFDerivAt
      rw [hev.fderiv_eq, hd.fderiv]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [add_comm]
      congr 1
      rw [fderiv_expand _ hy, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [mul_smul]
      rfl

theorem Dw_eq_comb : ∀ (n : ℕ) (L : List (Idx n)), ∃ (m : ℕ) (c : Fin m → Mat n → ℝ) (w : Fin m → List (Idx n)),
    (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
      ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  intro n L
  obtain ⟨ι, _, c, w, hc, h⟩ := exists_integralCombination_of_mem_completedLattice L
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => c (e.symm i), fun i => w (e.symm i), fun i => hc _, ?_⟩
  intro V _ _ f hf y hy
  rw [h V f hf y hy]
  exact (Equiv.sum_comp e.symm fun i => c i y • Rw (w i) f y).symm

end GlobalTheory.CompanionTheory.SobGL.Expand

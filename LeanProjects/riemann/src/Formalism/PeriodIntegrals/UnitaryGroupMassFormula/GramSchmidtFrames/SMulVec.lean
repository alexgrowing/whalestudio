import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.XiHermitianCofactorDet

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

abbrev Sm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (s : Set E) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f s

lemma sv_iff {m : ℕ} {v : E → Fin m → ℂ} : Sm v s ↔ ∀ i, Sm (fun x => v x i) s := by
  exact contDiffOn_pi

lemma sm_iff {p q : ℕ} {M : E → Matrix (Fin p) (Fin q) ℂ} : Sm M s ↔ ∀ i j, Sm (fun x => M x i j) s := by
  unfold Sm
  exact contDiffOn_pi.trans (forall_congr' fun i => contDiffOn_pi)

lemma s_star {f : E → ℂ} (hf : Sm f s) : Sm (fun x => star (f x)) s := by
  exact Complex.conjCLE.contDiff.comp_contDiffOn hf

lemma s_re {f : E → ℂ} (hf : Sm f s) : Sm (fun x => (f x).re) s := by
  exact Complex.reCLM.contDiff.comp_contDiffOn hf

lemma s_ofReal {f : E → ℝ} (hf : Sm f s) : Sm (fun x => ((f x : ℝ) : ℂ)) s := by
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hf

lemma s_mulVec {m : ℕ} {M : E → Matrix (Fin m) (Fin m) ℂ} {v : E → Fin m → ℂ} (hM : Sm M s) (hv : Sm v s) :
    Sm (fun x => M x *ᵥ v x) s := by
  rw [sv_iff]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun j _ => (sm_iff.1 hM i j).mul (sv_iff.1 hv j)

lemma s_herm {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) {v w : E → Fin m → ℂ} (hv : Sm v s) (hw : Sm w s) :
    Sm (fun x => herm H (v x) (w x)) s := by
  have hH : Sm (fun x => H *ᵥ v x) s := s_mulVec contDiffOn_const hv
  simp only [herm, dotProduct, Pi.star_apply]
  exact ContDiffOn.sum fun i _ => (s_star (sv_iff.1 hw i)).mul (sv_iff.1 hH i)

lemma s_smul {m : ℕ} {c : E → ℂ} {v : E → Fin m → ℂ} (hc : Sm c s) (hv : Sm v s) :
    Sm (fun x => c x • v x) s := by
  rw [sv_iff]
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  exact hc.mul (sv_iff.1 hv i)

lemma s_mmul {m : ℕ} {A B : E → Matrix (Fin m) (Fin m) ℂ} (hA : Sm A s) (hB : Sm B s) :
    Sm (fun x => A x * B x) s := by
  rw [sm_iff]
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (sm_iff.1 hA i l).mul (sm_iff.1 hB l j)

lemma s_ct {m : ℕ} {A : E → Matrix (Fin m) (Fin m) ℂ} (hA : Sm A s) : Sm (fun x => (A x)ᴴ) s := by
  rw [sm_iff]
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact s_star (sm_iff.1 hA j i)

private lemma sm_finset_prod {ι : Type*} (u : Finset ι) {f : ι → E → ℂ} (h : ∀ i ∈ u, Sm (f i) s) :
    Sm (fun x => ∏ i ∈ u, f i x) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using contDiffOn_const
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma s_det {p : ℕ} {M : E → Matrix (Fin p) (Fin p) ℂ} (h : ∀ i j, Sm (fun x => M x i j) s) :
    Sm (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (sm_finset_prod _ fun i _ => h (σ i) i)

lemma s_adj {p : ℕ} {M : E → Matrix (Fin p) (Fin p) ℂ} (h : ∀ i j, Sm (fun x => M x i j) s) (a b : Fin p) :
    Sm (fun x => (M x).adjugate a b) s := by
  simp only [Matrix.adjugate_apply]
  refine s_det fun i j => ?_
  simp only [Matrix.updateRow_apply]
  by_cases hi : i = b
  · simp only [hi, if_true]
    exact contDiffOn_const
  · simp only [hi, if_false]
    exact h i j

variable {k r : ℕ}

lemma s_wbPart {v : E → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s) : Sm (fun x => wbPart k r (v x)) s := by
  rw [sv_iff]
  intro i
  simp only [wbPart]
  by_cases hc : r ≤ i.val ∧ i.val ≤ r + k
  · simp only [hc, and_self, if_true]
    exact sv_iff.1 hv i
  · simp only [hc, if_false]
    exact contDiffOn_const

lemma s_prW (z : Fin (2 * r + k + 1) → ℂ) {v : E → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s) :
    Sm (fun x => prW k r z (v x)) s := by
  simp only [prW]
  exact (s_wbPart hv).add (s_smul ((s_herm _ (s_wbPart hv) contDiffOn_const).div_const _) contDiffOn_const)

lemma s_Zhat (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) (a b : Fin (r + 1)) :
    Sm (fun x => Zhat k r z z' (Y x) a b) s := by
  simp only [Zhat]
  exact s_herm _ (s_mulVec hY contDiffOn_const) contDiffOn_const

lemma s_xcofL (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) :
    Sm (fun x => xcofL k r z z' (Y x)) s := by
  simp only [xcofL]
  exact ContDiffOn.sum fun a _ =>
    s_smul (s_star (s_adj (fun i j => s_Zhat z z' hY i j) _ _)) contDiffOn_const

lemma s_xcof (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) :
    Sm (fun x => xcof k r z z' (Y x)) s := by
  simp only [xcof]
  exact ContDiffOn.sum fun b _ =>
    s_smul (s_adj (fun i j => s_Zhat z z' hY i j) _ _) (s_mulVec hY contDiffOn_const)

lemma s_omW (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) :
    Sm (fun x => omW k r z z' (Y x)) s := by
  simp only [omW]
  exact s_prW z (s_xcof z z' hY)

end smooth

end PI.UnitaryGroupMassFormula.GsFr

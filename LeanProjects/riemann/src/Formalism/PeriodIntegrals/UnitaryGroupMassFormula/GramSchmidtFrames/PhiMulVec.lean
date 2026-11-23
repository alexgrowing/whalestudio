import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.LocBCore

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section loca

variable {k r : ℕ}

lemma aps {V : Type*} [AddCommGroup V] (a b : V) : a + (b - a) = b := by
  exact add_sub_cancel a b

lemma spa {V : Type*} [AddCommGroup V] (a b : V) : b - a + a = b := by
  exact sub_add_cancel b a

def Rk (k r : ℕ) (p q : Fin (2 * r + k + 1) → ℂ) : B.Mat k r := vecMulVec p (star q ᵥ* Hpk k r)

lemma Rk_mulVec (p q v : Fin (2 * r + k + 1) → ℂ) : Rk k r p q *ᵥ v = herm (Hpk k r) v q • p := by
  unfold Rk
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, ← Matrix.dotProduct_mulVec]
  rfl

def Dw (k r : ℕ) : B.Mat k r := diagonal fun i => if r ≤ i.val ∧ i.val ≤ r + k then 1 else 0

lemma Dw_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Dw k r *ᵥ v = wbPart k r v := by
  funext i
  simp [Dw, Matrix.mulVec_diagonal, wbPart]

def Pm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  Dw k r + ((Tz k r z : ℂ))⁻¹ • (Rk k r z z * Dw k r)

lemma Pm_mulVec (z v : Fin (2 * r + k + 1) → ℂ) : Pm k r z *ᵥ v = prW k r z v := by
  unfold Pm
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Dw_mulVec, Rk_mulVec, smul_smul]
  unfold prW
  rw [div_eq_inv_mul]

def wv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Fin (r + 1) → ℂ := fun a => herm (Hpk k r) (M *ᵥ u) (fvec k r z a)

def gam (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Fin (r + 1) → ℂ :=
  (-((Zhat k r z z' M).det)⁻¹) • ((Zhat k r z z' M).adjugate *ᵥ wv k r z M u)

def Lm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  1 + ∑ c : Fin (r + 1), ∑ a : Fin (r + 1),
    (-((Zhat k r z z' M).det)⁻¹ * (Zhat k r z z' M).adjugate c a) • (Rk k r (fvec k r z' c) (fvec k r z a) * M)

lemma Lm_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Lm k r z z' M *ᵥ u = u + ∑ c, gam k r z z' M u c • fvec k r z' c := by
  unfold Lm gam wv
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Rk_mulVec, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

def Phi (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  Pm k r z * M * Lm k r z z' M

lemma Phi_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Phi k r z z' M *ᵥ u = prW k r z (M *ᵥ (Lm k r z z' M *ᵥ u)) := by
  unfold Phi
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Pm_mulVec]

def ev (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  nz k r (omW k r z z' M)

def Am (k r : ℕ) (z z' nu : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  (1 - Pm k r z) + Phi k r z z' M * (Pm k r z - Rk k r nu nu * Pm k r z) + Rk k r (ev k r z z' M) nu * Pm k r z

lemma Am_mulVec (z z' nu : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    Am k r z z' nu M *ᵥ v = (v - prW k r z v) +
      Phi k r z z' M *ᵥ (prW k r z v - herm (Hpk k r) (prW k r z v) nu • nu) +
      herm (Hpk k r) (prW k r z v) nu • ev k r z z' M := by
  unfold Am
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Pm_mulVec,
    Rk_mulVec]

lemma s_msmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m : ℕ} {c : E → ℂ}
    {M : E → Matrix (Fin m) (Fin m) ℂ} (hc : Sm c s) (hM : Sm M s) : Sm (fun x => c x • M x) s :=
  sm_iff.2 fun i j => by simp only [Matrix.smul_apply, smul_eq_mul]; exact hc.mul (sm_iff.1 hM i j)

lemma s_Rk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {p : E → Fin (2 * r + k + 1) → ℂ}
    (hp : Sm p s) (q : Fin (2 * r + k + 1) → ℂ) : Sm (fun x => Rk k r (p x) q) s :=
  sm_iff.2 fun i j => by simp only [Rk, vecMulVec_apply]; exact (sv_iff.1 hp i).mul contDiffOn_const

lemma s_Am {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (z z' nu : Fin (2 * r + k + 1) → ℂ)
    {Y : E → B.Mat k r} (hY : Sm Y s) (hd : ∀ x ∈ s, (Zhat k r z z' (Y x)).det ≠ 0)
    (hn : ∀ x ∈ s, 0 < (herm (Hpk k r) (omW k r z z' (Y x)) (omW k r z z' (Y x))).re) :
    Sm (fun x => Am k r z z' nu (Y x)) s := by
  have hdi : Sm (fun x => -((Zhat k r z z' (Y x)).det)⁻¹) s := ((s_det (s_Zhat z z' hY)).inv hd).neg
  have hL : Sm (fun x => Lm k r z z' (Y x)) s := by
    unfold Lm
    exact contDiffOn_const.add (ContDiffOn.sum fun c _ => ContDiffOn.sum fun a _ =>
      s_msmul (hdi.mul (s_adj (s_Zhat z z' hY) c a)) (s_mmul contDiffOn_const hY))
  have hP : Sm (fun x => Phi k r z z' (Y x)) s := by
    unfold Phi
    exact s_mmul (s_mmul contDiffOn_const hY) hL
  have hf : Sm (fun x => (herm (Hpk k r) (omW k r z z' (Y x)) (omW k r z z' (Y x))).re) s :=
    s_re (s_herm _ (s_omW z z' hY) (s_omW z z' hY))
  have hN : Sm (fun x => ((Real.sqrt (herm (Hpk k r) (omW k r z z' (Y x)) (omW k r z z' (Y x))).re)⁻¹ : ℝ)) s :=
    (hf.sqrt fun x hx => (hn x hx).ne').inv fun x hx => (Real.sqrt_pos.2 (hn x hx)).ne'
  have he : Sm (fun x => ev k r z z' (Y x)) s := by
    unfold ev nz
    exact s_smul (s_ofReal hN) (s_omW z z' hY)
  unfold Am
  exact (contDiffOn_const.add (s_mmul hP contDiffOn_const)).add (s_mmul (s_Rk he nu) contDiffOn_const)

end loca

end PI.UnitaryGroupMassFormula.GsFr

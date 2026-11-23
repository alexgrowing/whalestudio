import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.PathVar

theorem uMat_inj {n : ℕ} {ε : Fin n → Bool} {a b : Formalism.REAL.UJ ε} (h : uMat a = uMat b) : a = b :=
  Subtype.ext (Units.ext h)

theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (s t : ℝ) :
    expU ((s + t) • X) = expU (s • X) * expU (t • X) := by
  apply uMat_inj
  rw [uMat_mul', uMat_expU, uMat_expU, uMat_expU, add_smul, Submodule.coe_add]
  apply Matrix.exp_add_of_commute
  simp only [Submodule.coe_smul]
  exact ((Commute.refl (X : Matrix (Fin n) (Fin n) ℂ)).smul_left s).smul_right t

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : expU ((0 : ℝ) • X) = 1 := by
  apply uMat_inj
  rw [uMat_expU, zero_smul, Submodule.coe_zero, NormedSpace.exp_zero]
  rfl

noncomputable def pt (B : RowsAut) (E : gInf B) (z : B.I.GA) (t : ℝ) : B.I.GA :=
  z * ((fun v => expU (t • E v)), 1)

theorem pt_add (B : RowsAut) (E : gInf B) (z : B.I.GA) (s t : ℝ) :
    pt B E z (s + t) = pt B E z s * ((fun v => expU (t • E v)), 1) := by
  unfold pt
  rw [mul_assoc]
  congr 1
  refine Prod.ext ?_ (by simp)
  funext v
  exact expU_add _ _ _

theorem pt_zero (B : RowsAut) (E : gInf B) (z : B.I.GA) : pt B E z 0 = z := by
  unfold pt
  have : (((fun v => expU ((0 : ℝ) • E v)), 1) : B.I.GA) = 1 := by
    refine Prod.ext ?_ rfl
    funext v
    exact expU_zero _
  rw [this, mul_one]

theorem hasDerivAt_vv (B : RowsAut) {D : ℕ} (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund))
    (Fr : Fin D → B.Hs → B.I.GA → ℂ) (h : ∀ i, IsReps B (T i) (Fr i)) {P : ℕ} {u : B.Hs} (hu : u ∈ VP B P)
    (E : gInf B) (z : B.I.GA) (s : ℝ) :
    HasDerivAt (fun t => vv B Fr u (pt B E z t)) (vv B Fr (dAct B E u) (pt B E z s)) s := by
  have h1 : ∀ i, HasDerivAt (fun t => Fr i u (pt B E z t)) (Fr i (dAct B E u) (pt B E z s)) s := by
    intro i
    have h0 := (h i P u hu).2.2 E (pt B E z s)
    rw [← sub_self s] at h0
    have h2 := h0.comp_sub_const s s
    simp only [← pt_add, add_sub_cancel] at h2
    exact h2
  have h2 : HasDerivAt (fun t => fun i => Fr i u (pt B E z t)) (fun i => Fr i (dAct B E u) (pt B E z s)) s :=
    hasDerivAt_pi.2 h1
  exact ((EuclideanSpace.equiv (Fin D) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2

theorem hs_smul_le {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    Formalism.REAL.hs (s • X) ≤ Formalism.REAL.hs X := by
  unfold Formalism.REAL.hs
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.smul_apply, norm_smul, Real.norm_of_nonneg h0]
  exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (norm_nonneg _) h1) 2

theorem pt_mem_omega (B : RowsAut) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (ρ : ℝ)
    (A Z : gInf B)
    (hρ : Real.sqrt (∑ v, Formalism.REAL.hs (A v).1) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v).1) ≤ ρ)
    (hN : ∀ s t : ℝ, ∃ m : B.I.Ginf, ((m, 1) : B.I.GA) ∈ B.I.NA W ∧
      ∀ v, uMat (m v) * uMat (x.1 v) =
        uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • (A v).1) * NormedSpace.exp ((t : ℂ) • (Z v).1))
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    pt B Z (pt B A x s) t ∈ omega B.I x W ρ := by
  refine ⟨by simp [pt], fun v => (s • A v).1, fun v => (t • Z v).1, fun v => ⟨(s • A v).2, (t • Z v).2⟩, ?_,
    fun v => rfl, fun s' t' => ?_⟩
  · refine le_trans (add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)) hρ
    · exact Finset.sum_le_sum fun v _ => hs_smul_le _ hs.1 hs.2
    · exact Finset.sum_le_sum fun v _ => hs_smul_le _ ht.1 ht.2
  · obtain ⟨m, hm, hm'⟩ := hN (s' * s) (t' * t)
    refine ⟨m, hm, fun v => ?_⟩
    rw [hm' v]
    simp only [Submodule.coe_smul, Complex.coe_smul, smul_smul]

theorem leg (B : RowsAut) (b M : ℝ) (P : ℕ) {D : ℕ} (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund))
    (Fr : Fin D → B.Hs → B.I.GA → ℂ) (hS : StepBoundAt B b P) (h : ∀ i, IsReps B (T i) (Fr i)) (hM : 0 ≤ M)
    (E : gInf B) (z : B.I.GA)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ VP B (P + 1), ‖vv B Fr u (pt B E z t)‖ ≤ M * ‖u‖)
    {u : B.Hs} (hu : u ∈ VP B P) :
    ‖vv B Fr u (pt B E z 1) - vv B Fr u z‖ ≤
      Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := by
  have := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t => vv B Fr u (pt B E z t)) (f' := fun s => vv B Fr (dAct B E u) (pt B E z s))
    (C := Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖))
    (fun s _ => (hasDerivAt_vv B T Fr h hu E z s).hasDerivWithinAt)
    (fun s hs => by
      refine (hb s (Set.Ico_subset_Icc_self hs) _ (hS.2.2.2.2.2.2 E u hu)).trans ?_
      refine (mul_le_mul_of_nonneg_left (hS.2.2.2.2.2.1 E u hu) hM).trans (le_of_eq ?_)
      ring)
  simpa only [pt_zero] using this

theorem path_variation : ∀ (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)), StepBoundAt B b P → (∀ i, IsReps B (T i) (Fr i)) → 0 ≤ M → (∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P, ‖vv B Fr u y - vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  intro B b ρ M P D T Fr x W hS h hM hb y hy u hu
  obtain ⟨hy2, A0, Z0, hg, hρ, hy1, hN⟩ := hy
  let A : gInf B := fun v => ⟨A0 v, (hg v).1⟩
  let Z : gInf B := fun v => ⟨Z0 v, (hg v).2⟩
  have hmem := fun s t hs ht => pt_mem_omega B x W ρ A Z hρ hN (s := s) (t := t) hs ht
  have hyeq : y = pt B Z (pt B A x 1) 1 := by
    refine Prod.ext ?_ (by simp [pt, hy2])
    funext v
    apply uMat_inj
    rw [hy1 v]
    simp only [pt, one_smul]
    rfl
  have h1 := leg B b M P T Fr hS h hM A x (fun t ht w hw => by
    have := hb _ (hmem t 0 ht (by simp)) w hw
    rwa [pt_zero] at this) hu
  have h2 := leg B b M P T Fr hS h hM Z (pt B A x 1) (fun t ht w hw => hb _ (hmem 1 t (by simp) ht) w hw) hu
  have hK : 0 ≤ Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
    unfold beP; positivity
  rw [← hyeq] at h2
  calc _ ≤ ‖vv B Fr u y - vv B Fr u (pt B A x 1)‖ + ‖vv B Fr u (pt B A x 1) - vv B Fr u x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (Real.sqrt (∑ v, Formalism.REAL.hs (A0 v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z0 v))) *
        (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := by
        rw [add_mul, add_comm]; exact add_le_add h1 h2
    _ ≤ ρ * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := mul_le_mul_of_nonneg_right hρ hK
    _ = _ := by ring

end GlobalTheory.PathVar

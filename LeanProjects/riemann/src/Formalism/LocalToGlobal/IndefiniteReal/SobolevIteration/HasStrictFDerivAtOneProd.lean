import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.HasStrictFDerivAtCay

noncomputable section

open Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace Chart

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem oneProd_succ {d : ℕ} (Y : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (t : Fin (d + 1) → ℝ) :
    oneProd Y t = NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
  unfold oneProd
  rw [List.ofFn_succ, List.prod_cons]

theorem oneProd_zero : ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), oneProd Y 0 = 1 := by
  intro d Y
  simp [oneProd, NormedSpace.exp_zero]

theorem oneProd_mem (G : Matrix (Fin n) (Fin n) ℂ) :
    ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieG G) → ∀ t : Fin d → ℝ,
      oneProd Y t ∈ Formalism.QuantumDeterminants.UH G := by
  intro d
  induction d with
  | zero =>
    intro Y _ t
    have h1 : oneProd Y t = 1 := by simp [oneProd]
    rw [h1]
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
    simp
  | succ d ih =>
    intro Y hY t
    rw [oneProd_succ]
    exact mul_mem_UH₂ G _ (expS_mem_UH (hY 0) (t 0)) _ (ih _ (fun i => hY i.succ) _)

def lin {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (Y i)

theorem lin_apply {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) :
    lin Y t = ∑ i, t i • Y i := by
  unfold lin
  simp

theorem hasStrictFDerivAt_oneProd : ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ),
    HasStrictFDerivAt (oneProd Y) (lin Y) 0 := by
  intro d
  induction d with
  | zero =>
    intro Y
    have h1 : oneProd Y = fun _ => 1 := funext fun t => by simp [oneProd]
    have h2 : lin Y = 0 := ContinuousLinearMap.ext fun t => by simp [lin_apply]
    rw [h1, h2]
    exact hasStrictFDerivAt_const _ _
  | succ d ih =>
    intro Y
    have hsplit : oneProd Y = fun t : Fin (d + 1) → ℝ =>
        NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) :=
      funext fun t => oneProd_succ Y t
    let L0 : (Fin (d + 1) → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      (ContinuousLinearMap.proj (0 : Fin (d + 1))).smulRight (Y 0)
    let T : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
    have ha : HasStrictFDerivAt (fun t : Fin (d + 1) → ℝ => NormedSpace.exp (t 0 • Y 0)) L0 0 := by
      have hz : L0 0 = 0 := map_zero L0
      have he : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
          (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (L0 0) := by
        rw [hz]
        exact hasStrictFDerivAt_exp_zero
      exact (he.comp (0 : Fin (d + 1) → ℝ) L0.hasStrictFDerivAt).congr_fderiv
        (ContinuousLinearMap.ext fun t => rfl)
    have hb : HasStrictFDerivAt (fun t : Fin (d + 1) → ℝ => oneProd (fun i => Y i.succ) (fun i => t i.succ))
        ((lin fun i => Y i.succ).comp T) 0 := by
      have hz : T 0 = 0 := map_zero T
      have hi : HasStrictFDerivAt (oneProd fun i => Y i.succ) (lin fun i => Y i.succ) (T 0) := by
        rw [hz]
        exact ih _
      exact hi.comp (0 : Fin (d + 1) → ℝ) T.hasStrictFDerivAt
    have hb0 : oneProd (fun i => Y i.succ) (fun _ => (0 : ℝ)) = 1 := oneProd_zero _
    have hm := ha.mul' hb
    rw [hsplit]
    refine hm.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun t => ?_
    have e1 : NormedSpace.exp ((0 : Fin (d + 1) → ℝ) 0 • Y 0) = 1 := by simp
    have e2 : oneProd (fun i => Y i.succ) (fun i => (0 : Fin (d + 1) → ℝ) i.succ) = 1 := hb0
    show NormedSpace.exp ((0 : Fin (d + 1) → ℝ) 0 • Y 0) * (lin (fun i => Y i.succ) (T t)) +
      L0 t * oneProd (fun i => Y i.succ) (fun i => (0 : Fin (d + 1) → ℝ) i.succ) = lin Y t
    rw [e1, e2, one_mul, mul_one, lin_apply, lin_apply, Fin.sum_univ_succ]
    exact add_comm _ _

end Chart

end Formalism.IndefR.Tow.SobPf

end

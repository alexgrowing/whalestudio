import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.ParClosed

variable {D : D7}

theorem chS_succ (c : Com D) (k : ℕ) : c.chS (k + 1) = c.μ (k + 1) * c.eps (k + 1) := by
  unfold Com.chS Com.eps Lift.chrStep
  split_ifs <;> simp

theorem chT_succ (c : Com D) (k : ℕ) : c.chT (k + 1) = c.μ (k + 1) * c.eps k := by
  unfold Com.chT Com.eps Lift.chrStep
  rcases Nat.even_or_odd k with hk | hk
  · have h1 : Odd (k + 1) := hk.add_one
    have h2 : ¬ Odd k := Nat.not_odd_iff_even.2 hk
    simp [h1, h2]
  · have h1 : ¬ Odd (k + 1) := Nat.not_odd_iff_even.2 hk.add_one
    simp [h1, hk]

theorem eps_succ (c : Com D) (k : ℕ) :
    c.chS (k + 1) * (c.chT (k + 1))⁻¹ * c.eps k = c.eps (k + 1) := by
  rw [chS_succ, chT_succ]
  exact by
    have h : ∀ a b e : (AE D)ˣ →* Circle, a * b * (a * e)⁻¹ * e = b := fun a b e => by
      rw [_root_.mul_inv_rev, mul_comm e⁻¹ a⁻¹, mul_comm a b]
      simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one]
    exact h _ _ _

abbrev vf (χ : (AE D)ˣ →* Circle) : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := GlobalTheory.LFun.val (F := D.host.F) χ

theorem vf_mul (χ ψ : (AE D)ˣ →* Circle) : vf (χ * ψ) = vf χ * vf ψ := by
  funext w; simp [vf]

theorem twist_sum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → GlobalTheory.LFun.Fam K)
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : GlobalTheory.LFun.twist (∑ i ∈ s, f i) z = ∑ i ∈ s, GlobalTheory.LFun.twist (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => funext w; simp [GlobalTheory.LFun.twist]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LFun.twist_add, ih]

theorem stepPar_eq (χS χT : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) :
    stepPar χS χT t B = GlobalTheory.LFun.twist B (vf (χS * χT⁻¹)) + GlobalTheory.LFun.segFam (vf χS) t := by
  funext w; simp [stepPar, GlobalTheory.LFun.twist, GlobalTheory.LFun.segFam, vf]

theorem chainPar_closed (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B k = GlobalTheory.LFun.twist (B + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i)) D.R.t) (vf (c.eps k)) := by
  induction k with
  | zero =>
    have h1 : vf (1 : (AE D)ˣ →* Circle) = 1 := funext fun w => GlobalTheory.LFun.val_one (F := D.host.F) w
    simp [chainPar, Com.eps, h1]
  | succ k ih =>
    rw [chainPar_succ, ih, stepPar_eq, GlobalTheory.LFun.twist_twist, ← vf_mul, eps_succ, Finset.sum_Icc_succ_top (by omega),
      ← add_assoc, GlobalTheory.LFun.twist_add (B + _), GlobalTheory.LFun.twist_segFam, ← vf_mul, chS_succ, mul_comm (c.eps (k + 1))]

theorem twist_vf (μ e : (AE D)ˣ →* Circle) : (vf (μ * e))⁻¹ * vf e = (vf μ)⁻¹ := by
  funext w; simp [vf, mul_comm]

theorem vf_quot (μ ν : (AE D)ˣ →* Circle) : (vf ν)⁻¹ * vf μ = vf (μ * ν⁻¹) := by
  funext w; simp [vf, mul_comm]

end GlobalTheory.ChainOnto.ParClosed

open GlobalTheory.ChainOnto.ParClosed in

theorem GlobalTheory.ChainOnto.chainPar_twist_chT : ∀ (D : D7) (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ),
    GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ =
      GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ +
        ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t := by
  intro D c B k
  change GlobalTheory.LFun.twist (chainPar c B k) (vf (c.chT (k + 1)))⁻¹ =
    GlobalTheory.LFun.twist B (vf (c.μ (k + 1)))⁻¹ + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t
  rw [chainPar_closed, GlobalTheory.LFun.twist_twist, chT_succ, twist_vf, GlobalTheory.LFun.twist_add, twist_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.LFun.twist_segFam, vf_quot]

end

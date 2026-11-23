import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def selL {D E : ℕ} (σ : Fin E → Fin D) : (Fin D → ℂ) →L[ℂ] (Fin E → ℂ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (σ a)

theorem selL_apply {D E : ℕ} (σ : Fin E → Fin D) (z : Fin D → ℂ) (a : Fin E) :
    selL σ z a = z (σ a) := rfl

theorem jacC_selL {D E : ℕ} (σ : Fin E → Fin D) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.A.jacC (selL σ) z = Matrix.of fun a k => if σ a = k then (1 : ℂ) else 0 := by
  ext a k
  simp [ReciprocityTheory.AnForm.A.jacC, ContinuousLinearMap.fderiv, selL_apply, Pi.single_apply]

theorem hessC_selL_apply {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (i j : Fin D) :
    hessC (φ ∘ selL σ) z i j = ∑ b, (∑ a, (if σ a = i then (1 : ℂ) else 0) *
      hessC φ (selL σ z) a b) * (if σ b = j then (1 : ℂ) else 0) := by
  rw [ReciprocityTheory.AnForm.A.hessC_comp φ (selL σ) z ((selL σ).analyticAt z) hφ, jacC_selL]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  split_ifs <;> simp

theorem hessC_selL_inj {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) {σ : Fin E → Fin D}
    (hσ : Function.Injective σ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (a b : Fin E) :
    hessC (φ ∘ selL σ) z (σ a) (σ b) = hessC φ (selL σ z) a b := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hσ.eq_iff]

theorem hessC_selL_left {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) {i : Fin D} (hi : ∀ a, σ a ≠ i) (j : Fin D) :
    hessC (φ ∘ selL σ) z i j = 0 := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hi]

theorem hessC_selL_right {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (i : Fin D) {j : Fin D} (hj : ∀ a, σ a ≠ j) :
    hessC (φ ∘ selL σ) z i j = 0 := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hj]

theorem contDiffAt_comp_selL {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) : ContDiffAt ℝ 2 (φ ∘ selL σ) z :=
  ContDiffAt.comp z hφ ((selL σ).restrictScalars ℝ).contDiff.contDiffAt

def selA {d : ℕ} (c : Fin (d + 2)) : Fin (d + 1) → Fin (d + 2) :=
  Fin.cons c fun i : Fin d => i.succ.succ

def selT {d : ℕ} : Fin d → Fin (d + 2) := fun i => i.succ.succ

theorem selT_injective {d : ℕ} : Function.Injective (selT (d := d)) := fun a b h =>
  Fin.succ_injective _ (Fin.succ_injective _ h)

theorem selA_injective {d : ℕ} {c : Fin (d + 2)} (hc : ∀ i : Fin d, i.succ.succ ≠ c) :
    Function.Injective (selA c) := by
  intro a b h
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => rfl
    | succ b => exact absurd h.symm (by simpa [selA] using hc b)
  | succ a =>
    induction b using Fin.cases with
    | zero => exact absurd h (by simpa [selA] using hc a)
    | succ b =>
      have : a.succ.succ = b.succ.succ := by simpa [selA] using h
      rw [Fin.succ_injective _ (Fin.succ_injective _ this)]

theorem selA_eq_cons {d : ℕ} (c : Fin (d + 2)) (z : Fin (d + 2) → ℂ) :
    selL (selA c) z = Fin.cons (z c) (Fin.tail (Fin.tail z)) := by
  funext a
  induction a using Fin.cases with
  | zero => simp [selL_apply, selA]
  | succ a => simp [selL_apply, selA, Fin.tail]

theorem selT_eq_tail {d : ℕ} (z : Fin (d + 2) → ℂ) :
    selL selT z = Fin.tail (Fin.tail z) := rfl

theorem blk_zero_zero {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) : blk e B 0 0 = e := rfl

theorem blk_zero_succ {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (q : Fin d) :
    blk e B 0 q.succ = 0 := rfl

theorem blk_succ_zero {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (p : Fin d) :
    blk e B p.succ 0 = 0 := rfl

theorem blk_succ_succ {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d) :
    blk e B p.succ q.succ = B p q := rfl

theorem blk_assemble {d : ℕ} (T₀ T₁ T₂ : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ) (e₀ e₁ s t v : ℂ)
    (B₀ B₁ C : Matrix (Fin d) (Fin d) ℂ)
    (a₀ : ∀ a b, T₀ (selA 0 a) (selA 0 b) = blk e₀ B₀ a b)
    (l₀ : ∀ j, T₀ (Fin.succ 0) j = 0) (r₀ : ∀ i, T₀ i (Fin.succ 0) = 0)
    (a₁ : ∀ a b, T₁ (selA (Fin.succ 0) a) (selA (Fin.succ 0) b) = blk e₁ B₁ a b)
    (l₁ : ∀ j, T₁ 0 j = 0) (r₁ : ∀ i, T₁ i 0 = 0)
    (a₂ : ∀ a b, T₂ (selT a) (selT b) = C a b)
    (l₂ : ∀ j, T₂ 0 j = 0) (r₂ : ∀ i, T₂ i 0 = 0)
    (l₂' : ∀ j, T₂ (Fin.succ 0) j = 0) (r₂' : ∀ i, T₂ i (Fin.succ 0) = 0) :
    s • T₀ + t • T₁ + v • T₂ = blk (s * e₀) (blk (t * e₁) (s • B₀ + t • B₁ + v • C)) := by
  have p00 : T₀ 0 0 = e₀ := a₀ 0 0
  have p0k : ∀ k : Fin d, T₀ 0 k.succ.succ = 0 := fun k => a₀ 0 k.succ
  have pk0 : ∀ k : Fin d, T₀ k.succ.succ 0 = 0 := fun k => a₀ k.succ 0
  have pkl : ∀ k l : Fin d, T₀ k.succ.succ l.succ.succ = B₀ k l := fun k l => a₀ k.succ l.succ
  have q11 : T₁ (Fin.succ 0) (Fin.succ 0) = e₁ := a₁ 0 0
  have q1k : ∀ k : Fin d, T₁ (Fin.succ 0) k.succ.succ = 0 := fun k => a₁ 0 k.succ
  have qk1 : ∀ k : Fin d, T₁ k.succ.succ (Fin.succ 0) = 0 := fun k => a₁ k.succ 0
  have qkl : ∀ k l : Fin d, T₁ k.succ.succ l.succ.succ = B₁ k l := fun k l => a₁ k.succ l.succ
  have wkl : ∀ k l : Fin d, T₂ k.succ.succ l.succ.succ = C k l := fun k l => a₂ k l
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp only [p00, l₁, l₂, blk_zero_zero, mul_zero, add_zero]
    | succ j =>
      induction j using Fin.cases with
      | zero => simp only [r₀, l₁, l₂, blk_zero_succ, mul_zero, add_zero]
      | succ k => simp only [p0k, l₁, l₂, blk_zero_succ, mul_zero, add_zero]
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp only [l₀, r₁, l₂', blk_succ_zero, mul_zero, add_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => simp only [l₀, q11, l₂', blk_succ_succ, blk_zero_zero, mul_zero, add_zero, zero_add]
        | succ k => simp only [l₀, q1k, l₂', blk_succ_succ, blk_zero_succ, mul_zero, add_zero]
    | succ k =>
      induction j using Fin.cases with
      | zero => simp only [pk0, r₁, r₂, blk_succ_zero, mul_zero, add_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => simp only [r₀, qk1, r₂', blk_succ_succ, blk_succ_zero, mul_zero, add_zero]
        | succ l =>
          simp only [pkl, qkl, wkl, blk_succ_succ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem hessC_row_square : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p₀ p₁ e₀ e₁ : ℂ)
    (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) (s t v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p₀ y) → ContDiffAt ℝ 2 f (Fin.cons p₁ y) → ContDiffAt ℝ 2 α y →
    hessC f (Fin.cons p₀ y) = blk e₀ B₀ → hessC f (Fin.cons p₁ y) = blk e₁ B₁ →
    hessC (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z)))
      (Fin.cons p₀ (Fin.cons p₁ y)) =
    blk ((s : ℂ) * e₀) (blk ((t : ℂ) * e₁) ((s : ℂ) • B₀ + (t : ℂ) • B₁ + (v : ℂ) • hessC α y)) := by
  intro d f α y p₀ p₁ e₀ e₁ B₀ B₁ s t v hf₀ hf₁ hα h₀ h₁
  have ho : (Fin.succ 0 : Fin (d + 2)) = 1 := by simp
  have hinj₀ : Function.Injective (selA (0 : Fin (d + 2))) :=
    selA_injective fun i => Fin.succ_ne_zero _
  have hinj₁ : Function.Injective (selA (Fin.succ 0 : Fin (d + 2))) :=
    selA_injective fun i h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  have q₀ : selL (selA 0) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) = Fin.cons p₀ y := by
    rw [selA_eq_cons]; simp [Fin.tail_cons]
  have q₁ : selL (selA (Fin.succ 0)) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) =
      Fin.cons p₁ y := by
    rw [selA_eq_cons]; simp [Fin.tail_cons]
  have q₂ : selL selT (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) = y := by
    rw [selT_eq_tail]; simp [Fin.tail_cons]
  have g₀ : ContDiffAt ℝ 2 f (selL (selA 0) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by
    rwa [q₀]
  have g₁ : ContDiffAt ℝ 2 f
      (selL (selA (Fin.succ 0)) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by rwa [q₁]
  have g₂ : ContDiffAt ℝ 2 α (selL selT (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by
    rwa [q₂]
  have c₀ := contDiffAt_comp_selL f _ _ g₀
  have c₁ := contDiffAt_comp_selL f _ _ g₁
  have c₂ := contDiffAt_comp_selL α _ _ g₂
  have E : (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z))) =
      fun z => (fun z => (fun z => s * (f ∘ selL (selA 0)) z) z +
        (fun z => t * (f ∘ selL (selA (Fin.succ 0))) z) z) z +
        (fun z => v * (α ∘ selL selT) z) z := by
    funext z
    simp only [Function.comp, selA_eq_cons, selT_eq_tail, ho]
  rw [E, hessC_add' _ _ _ ((contDiffAt_const.mul c₀).add (contDiffAt_const.mul c₁))
      (contDiffAt_const.mul c₂),
    hessC_add' _ _ _ (contDiffAt_const.mul c₀) (contDiffAt_const.mul c₁),
    hessC_const_mul', hessC_const_mul', hessC_const_mul']
  refine blk_assemble _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b; rw [hessC_selL_inj f hinj₀ _ g₀, q₀, h₀]
  · intro j
    refine hessC_selL_left f _ _ g₀ ?_ j
    intro a
    induction a using Fin.cases with
    | zero => exact (Fin.succ_ne_zero _).symm
    | succ a => exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  · intro i
    refine hessC_selL_right f _ _ g₀ i ?_
    intro a
    induction a using Fin.cases with
    | zero => exact (Fin.succ_ne_zero _).symm
    | succ a => exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  · intro a b; rw [hessC_selL_inj f hinj₁ _ g₁, q₁, h₁]
  · intro j
    refine hessC_selL_left f _ _ g₁ ?_ j
    intro a
    induction a using Fin.cases with
    | zero => exact Fin.succ_ne_zero (0 : Fin (d + 1))
    | succ a => exact Fin.succ_ne_zero (Fin.succ a)
  · intro i
    refine hessC_selL_right f _ _ g₁ i ?_
    intro a
    induction a using Fin.cases with
    | zero => exact Fin.succ_ne_zero (0 : Fin (d + 1))
    | succ a => exact Fin.succ_ne_zero (Fin.succ a)
  · intro a b; rw [hessC_selL_inj α selT_injective _ g₂, q₂]
  · intro j; exact hessC_selL_left α _ _ g₂ (fun a => Fin.succ_ne_zero _) j
  · intro i; exact hessC_selL_right α _ _ g₂ i (fun a => Fin.succ_ne_zero _)
  · intro j
    exact hessC_selL_left α _ _ g₂ (fun a h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)) j
  · intro i
    exact hessC_selL_right α _ _ g₂ i (fun a h => Fin.succ_ne_zero _ (Fin.succ_injective _ h))

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN

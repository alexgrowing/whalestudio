import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.KerAdj

theorem pairing_swap {α : Type*} [MeasurableSpace α] {ν : Measure α} [SFinite ν]
    (k : α → α → ℂ) (g f : α → ℂ)
    (h : Integrable (fun p : α × α => conj (g p.1) * k p.1 p.2 * f p.2) (ν.prod ν)) :
    Integrable (fun x => conj (∫ y, conj (k y x) * g y ∂ν) * f x) ν ∧
    Integrable (fun y => conj (g y) * ∫ x, k y x * f x ∂ν) ν ∧
    ∫ x, conj (∫ y, conj (k y x) * g y ∂ν) * f x ∂ν
      = ∫ y, conj (g y) * ∫ x, k y x * f x ∂ν ∂ν := by
  have hL : ∀ x, conj (∫ y, conj (k y x) * g y ∂ν) * f x
      = ∫ y, conj (g y) * k y x * f x ∂ν := by
    intro x
    rw [← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  have hR : ∀ y, conj (g y) * ∫ x, k y x * f x ∂ν
      = ∫ x, conj (g y) * k y x * f x ∂ν := by
    intro y
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hL]
    exact h.swap.integral_prod_left
  · simp_rw [hR]
    exact h.integral_prod_left
  · simp_rw [hL, hR]
    exact (integral_integral_swap (f := fun y x => conj (g y) * k y x * f x) h).symm

theorem inner_eq_integral_conj_mul {α : Type*} [MeasurableSpace α] {ν : Measure α} (u v : Lp ℂ 2 ν) :
    inner ℂ u v = ∫ x, conj ((u : α → ℂ) x) * (v : α → ℂ) x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem entry_pairing (hK : KerBasic) (hR : RowInt) (hS : SchurInt) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (g f : Lp ℂ 2 X.ν) :
    Integrable (fun x => conj (∫ y, ker X.Γ (adj φ) x y * (g : X.G → ℂ) y ∂X.ν) * (f : X.G → ℂ) x) X.ν ∧
    Integrable (fun y => conj ((g : X.G → ℂ) y) * ∫ x, ker X.Γ φ y x * (f : X.G → ℂ) x ∂X.ν) X.ν ∧
    ∫ x, conj (∫ y, ker X.Γ (adj φ) x y * (g : X.G → ℂ) y ∂X.ν) * (f : X.G → ℂ) x ∂X.ν
      = ∫ y, conj ((g : X.G → ℂ) y) * ∫ x, ker X.Γ φ y x * (f : X.G → ℂ) x ∂X.ν ∂X.ν := by
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  obtain ⟨-, hc, -, -, hadj, -⟩ := hK X φ hφ
  obtain ⟨A, hA, h1, h2⟩ := hR X φ hφ
  have hg : MemLp (fun y => conj ((g : X.G → ℂ) y)) 2 X.ν := (Lp.memLp g).star
  have hI := hS X.G X.ν (ker X.Γ φ) A hc.measurable hA h1 h2 _ _ hg (Lp.memLp f)
  have := pairing_swap (ν := X.ν) (ker X.Γ φ) (g : X.G → ℂ) (f : X.G → ℂ) hI
  simpa only [hadj] using this

theorem opAdj_of : KerBasic → RowInt → SchurInt → OpExA → OpAdj := by
  intro hK hR hS hE X ι _ Φ T hΦ hT
  have hadj : ∀ i j, Tst (adj (Φ j i)) := fun i j => (hK X _ (hΦ j i)).2.2.2.1
  obtain ⟨T', hT', -⟩ := hE X ι (fun i j => adj (Φ j i)) hadj
  have hEq : T' = ContinuousLinearMap.adjoint T := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro g f
    have key := fun i j => entry_pairing hK hR hS X (Φ j i) (hΦ j i) (g j) (f i)
    have hl : ∀ i, inner ℂ (T' g i) (f i)
        = ∑ j, ∫ x, conj (∫ y, ker X.Γ (adj (Φ j i)) x y * (g j : X.G → ℂ) y ∂X.ν)
            * (f i : X.G → ℂ) x ∂X.ν := by
      intro i
      rw [inner_eq_integral_conj_mul, ← integral_finset_sum _ fun j _ => (key i j).1]
      refine integral_congr_ae ?_
      filter_upwards [hT' g i] with x hx
      rw [hx, map_sum, Finset.sum_mul]
    have hr : ∀ j, inner ℂ (g j) (T f j)
        = ∑ i, ∫ y, conj ((g j : X.G → ℂ) y)
            * ∫ x, ker X.Γ (Φ j i) y x * (f i : X.G → ℂ) x ∂X.ν ∂X.ν := by
      intro j
      rw [inner_eq_integral_conj_mul, ← integral_finset_sum _ fun i _ => (key i j).2.1]
      refine integral_congr_ae ?_
      filter_upwards [hT f j] with y hy
      rw [hy, Finset.mul_sum]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp_rw [hl, hr]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => (key i j).2.2
  rw [← hEq]
  exact hT'

end GlobalTheory.CompanionTheory.KerAdj

end

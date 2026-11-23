import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnDbarCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibnizStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCompHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtPullbackFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZeroStatement
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem dbarAt_congr {n : ℕ} {γ δ : V n → Alt n} {v : V n} (h : γ =ᶠ[𝓝 v] δ) :
    dbarAt γ v = dbarAt δ v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS : (fun x => (bas n).repr (γ x) S) =ᶠ[𝓝 v] fun x => (bas n).repr (δ x) S := h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx
  show GlobalTheory.dbar _ v (coordVec a) • _ = GlobalTheory.dbar _ v (coordVec a) • _
  rw [GlobalTheory.dbar_congr hS]

theorem dbarAt_eq_sum {n : ℕ} (β : V n → Alt n) (w : V n) :
    dbarAt β w = ∑ S, (∑ b, GlobalTheory.dbar (fun y => (bas n).repr (β y) S) w (coordVec b) • dzb b) * bas n S := by
  simp only [dbarAt, coefwise, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_comm

theorem dbarAt_pull_comp {n m : ℕ} {φ : V n → V m} {U : Set (V n)} (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) {v : V n} (hv : v ∈ U) {β : V m → Alt m}
    (hβ : ∀ S, DifferentiableAt ℝ (fun w => (bas m).repr (β w) S) (φ v)) :
    dbarAt (fun x => pull (fderiv ℂ φ x) (β (φ x))) v = pull (fderiv ℂ φ v) (dbarAt β (φ v)) := by
  have hφv : DifferentiableAt ℂ φ v := hφ.differentiableAt (hU.mem_nhds hv)
  have e1 : (fun x => pull (fderiv ℂ φ x) (β (φ x))) =
      fun x => ∑ S, (fun S y => (bas m).repr (β (φ y)) S) S x • (fun S y => pull (fderiv ℂ φ y) (bas m S)) S x := by
    funext x
    conv_lhs => rw [← (bas m).sum_repr (β (φ x)), map_sum]
    exact Finset.sum_congr rfl fun S _ => map_smul _ _ _
  rw [e1, GlobalTheory.T.dbar_sum_leibniz (c := fun S y => (bas m).repr (β (φ y)) S) (F := fun S y => pull (fderiv ℂ φ y) (bas m S)) (fun S => (hβ S).comp v (hφv.restrictScalars ℝ))
    (fun S T => GlobalTheory.T.differentiableAt_pullback_form hU hφ hv _ T)]
  simp only [GlobalTheory.T.dbar_pullback_holomorphic_zero hU hφ hv, smul_zero, add_zero]
  rw [dbarAt_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [GlobalTheory.T.dbar_comp_holomorphic hφv (hβ S), map_mul]

theorem isForm_dbar {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld)
    (h : A.IsForm α) : A.IsForm (A.dbar α) := by
  have hloc : ∀ i, ∀ v ∈ (A.e i).target, A.loc (A.dbar α) i v = dbarAt (A.loc α i) v := by
    intro i v hv
    rw [HolAtlas.loc, dif_pos hv]
    show dbarAt (A.loc α i) ((A.e i) ((A.e i).symm v)) = _
    rw [(A.e i).right_inv hv]
  refine ⟨fun i S => ?_, fun x x' hxx' => ?_⟩
  · exact (GlobalTheory.T.contDiffOn_dbar_coefficients (A.e i).open_target (h.smooth i) S).congr fun v hv => by rw [hloc i v hv]
  · have hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      x.ch.isOpen_inter_preimage_symm x'.ch.open_source
    have hφ : DifferentiableOn ℂ (x'.ch ∘ x.ch.symm) (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      A.holo x.1.1 x'.1.1
    have e : x.ch.symm (x.ch x.pt) = x'.pt := (x.ch.left_inv x.2).trans hxx'
    have hv0 : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source := by
      refine ⟨x.ch.map_source x.2, ?_⟩
      show x.ch.symm (x.ch x.pt) ∈ x'.ch.source
      rw [e]
      exact x'.2
    have hφv0 : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
      show x'.ch (x.ch.symm (x.ch x.pt)) = x'.ch x'.pt
      rw [e]
    have key : ∀ v ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source,
        A.loc α x.1.1 v = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) v) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) v)) := by
      intro v hv
      rw [HolAtlas.loc, dif_pos hv.1]
      have := h.compat ⟨(x.1.1, x.ch.symm v), x.ch.map_target hv.1⟩ ⟨(x'.1.1, x.ch.symm v), hv.2⟩ rfl
      have e2 : x.ch (x.ch.symm v) = v := x.ch.right_inv hv.1
      simp only [HolAtlas.Pt.crd, HolAtlas.Pt.ch, HolAtlas.Pt.pt] at this
      rw [this, e2]
      exact congrArg _ (HolAtlas.loc_crd A α ⟨(x'.1.1, x.ch.symm v), hv.2⟩).symm
    show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)
    rw [dbarAt_congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hv0) key),
      dbarAt_pull_comp hU hφ hv0 (β := A.loc α x'.1.1) (fun S => ?_), hφv0]
    rw [hφv0]
    exact ((h.smooth x'.1.1 S).contDiffAt (x'.ch.open_target.mem_nhds (x'.ch.map_source x'.2))).differentiableAt
      (by simp)

end GlobalTheory.CxForm

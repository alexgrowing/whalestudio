import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere

set_option autoImplicit false

noncomputable section

open Set
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.BcUnique

open GlobalTheory.CxForm

def headIn : V 1 →L[ℂ] V (1 + 1) :=
  (appendV 1 1 : V 1 × V 1 →L[ℂ] V (1 + 1)).comp (ContinuousLinearMap.inl ℂ (V 1) (V 1))

theorem headIn_apply (v : V 1) : headIn v = appendV 1 1 (v, 0) := rfl

theorem appendV_zero (v s : V 1) : appendV 1 1 (v, s) 0 = v 0 := rfl

theorem appendV_last (v s : V 1) : appendV 1 1 (v, s) (Fin.last 1) = s 0 := rfl

def sphFin : sphere.ι := (0 : Fin 2)

theorem sphFin_apply (w : ℂ) : sphere.e sphFin (w : OnePoint ℂ) = EuclideanSpace.single 0 w := by
  ext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [EuclideanSpace.single_apply, if_true]
  rfl

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (j : A.ι) (k : sphere.ι)

theorem famAtlas_symm (x : V (n + 1)) : ((famAtlas A).e (j, k)).symm x =
    ((A.e j).symm ((appendV n 1).symm x).1, (sphere.e k).symm ((appendV n 1).symm x).2) := rfl

theorem famAtlas_symm_appendV (v : V n) (s : V 1) : ((famAtlas A).e (j, k)).symm (appendV n 1 (v, s)) =
    ((A.e j).symm v, (sphere.e k).symm s) := by
  rw [famAtlas_symm, ContinuousLinearEquiv.symm_apply_apply]

theorem mem_famAtlas_target (x : V (n + 1)) : x ∈ ((famAtlas A).e (j, k)).target ↔
    ((appendV n 1).symm x).1 ∈ (A.e j).target ∧ ((appendV n 1).symm x).2 ∈ (sphere.e k).target := Iff.rfl

theorem appendV_mem_famAtlas_target (v : V n) (s : V 1) : appendV n 1 (v, s) ∈ ((famAtlas A).e (j, k)).target ↔
    v ∈ (A.e j).target ∧ s ∈ (sphere.e k).target := by
  rw [mem_famAtlas_target, ContinuousLinearEquiv.symm_apply_apply]

theorem smoothOn_fst {χ : M → ℂ} (hχ : A.SmoothOn univ χ) : (famAtlas A).SmoothOn univ fun y => χ y.1 := by
  rintro ⟨j, k⟩
  have d : ContDiff ℝ (⊤ : ℕ∞) fun x : V (n + 1) => ((appendV n 1).symm x).1 :=
    contDiff_fst.comp (((appendV n 1).symm : V (n + 1) →L[ℂ] V n × V 1).restrictScalars ℝ).contDiff
  exact (hχ j).comp d.contDiffOn fun x hx => ⟨hx.1.1, trivial⟩

end GlobalTheory.BcUnique

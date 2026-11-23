import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Matrix Topology
open scoped ContDiff

namespace GlobalTheory.LeviSliceGA

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

def lowL (hr : r ≤ a) : Lie E (a - r) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr) (GlobalTheory.LeviGA.blkEquiv hr)
        (Matrix.fromBlocks 0 0 0 (Matrix.of y)))
      map_add' := fun y z => by
        funext i j
        obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
        obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
        rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply]
      map_smul' := fun c y => by
        funext i j
        obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
        obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
        rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply] }

theorem lowL_apply (hr : r ≤ a) (y : Lie E (a - r)) : lowL hr y = toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr)
    (GlobalTheory.LeviGA.blkEquiv hr) (Matrix.fromBlocks 0 0 0 (Matrix.of y))) := rfl

def affA (hr : r ≤ a) (y : Lie E (a - r)) : Lie E a :=
  lowL hr y + toL (Matrix.reindex (GlobalTheory.LeviGA.blkEquiv hr) (GlobalTheory.LeviGA.blkEquiv hr) (Matrix.fromBlocks 1 0 0 0))

theorem affA_val (hr : r ≤ a) (u : GL (Fin (a - r)) (Cinf E)) :
    affA hr (toL u.val) = toL (GlobalTheory.LeviGA.blkGL hr (1, u)).val := by
  rw [affA, lowL_apply, GlobalTheory.LeviGA.blkGL_val]
  funext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [toL, Matrix.reindex_apply]

theorem infGL_apply {n : ℕ} (g : GL (Fin n) (Cinf E)) (i j : Fin n) :
    (infGL E n g : Matrix (Fin n) (Fin n) (Ad E)) i j = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j -
      sInf E ((1 : Matrix (Fin n) (Fin n) (Cinf E)) i j) + sInf E ((g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := rfl

theorem blkGL_infGL (hr : r ≤ a) (u : GL (Fin (a - r)) (Cinf E)) :
    GlobalTheory.LeviGA.blkGL hr ((1 : GA E r), infGL E (a - r) u) = infGL E a (GlobalTheory.LeviGA.blkGL hr (1, u)) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rw [GlobalTheory.LeviGA.blkGL_apply, infGL_apply, GlobalTheory.LeviGA.blkGL_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, (GlobalTheory.LeviGA.blkEquiv hr).injective.eq_iff, infGL_apply]

theorem chart_slice (hr : r ≤ a) (m₁ : GA E r) (φ : GA E a → ℂ) (m₂ : GA E (a - r)) {y : Lie E (a - r)}
    (hy : y ∈ invSet E (a - r)) :
    chart (fun m : GA E (a - r) => φ (GlobalTheory.LeviGA.blkGL hr (m₁, m))) m₂ y =
      chart φ (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) (affA hr y) := by
  obtain ⟨u, hu⟩ := hy
  have e : y = toL u.val := hu.symm
  subst e
  rw [chart_val, affA_val, chart_val, ← blkGL_infGL, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem affA_one (hr : r ≤ a) : affA hr (oneL E (a - r)) = oneL E a := by
  have h := affA_val (E := E) hr 1
  rw [show ((1 : GL (Fin r) (Cinf E)), (1 : GL (Fin (a - r)) (Cinf E))) = 1 from rfl, map_one] at h
  exact h

theorem hasFDerivAt_affA (hr : r ≤ a) (y : Lie E (a - r)) : HasFDerivAt (affA hr) (lowL (E := E) hr) y :=
  (lowL hr).hasFDerivAt.add_const _

theorem lowL_single (hr : r ≤ a) (p p' : Fin (a - r)) (x : Cinf E) :
    lowL hr (toL (Matrix.single p p' x)) =
      toL (Matrix.single (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) x) := by
  rw [lowL_apply]
  funext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.LeviGA.blkEquiv hr).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [toL, Matrix.reindex_apply, Matrix.single_apply, (GlobalTheory.LeviGA.blkEquiv hr).injective.eq_iff] <;>
    by_cases hi : i = p <;> by_cases hj : j = p' <;> simp [hi, hj, Pi.single_apply] <;> intros <;> simp_all

theorem slice_mem_Sm (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a) :
    (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) := fun m₂ =>
  ((f.2 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))).comp ((lowL (E := E) hr).contDiff.add contDiff_const).contDiffOn
    (fun y hy => by
      obtain ⟨u, hu⟩ := hy
      have e : y = toL u.val := hu.symm
      subst e
      show affA hr _ ∈ _
      rw [affA_val]
      exact val_mem_invSet _)).congr fun y hy => chart_slice hr m₁ f.1 m₂ hy

theorem lieS_slice (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a) (p p' : Fin (a - r)) (ψ : Sm E (a - r))
    (hψ : ψ.1 = fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) (x : Cinf E) (m₂ : GA E (a - r)) :
    (lieS E (a - r) p p' x ψ).1 m₂ =
      (lieS E a (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) x f).1
        (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  rw [GlobalTheory.CuspRep.lieS_apply, GlobalTheory.CuspRep.lieS_apply, GlobalTheory.CuspRep.lie_apply, GlobalTheory.CuspRep.lie_apply, lieD, lieD, hψ]
  have ev : chart (fun m : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m))) m₂ =ᶠ[𝓝 (oneL E (a - r))]
      chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) ∘ affA hr :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun y hy => chart_slice hr m₁ f.1 m₂ hy
  have hd : HasFDerivAt (chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)))
      (fderiv ℝ (chart f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) (oneL E a)) (affA hr (oneL E (a - r))) := by
    rw [affA_one]; exact (differentiableAt_chart f.2 _).hasFDerivAt
  rw [ev.fderiv_eq, (hd.comp (oneL E (a - r)) (hasFDerivAt_affA hr _)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, lowL_single]

theorem slice_smooth_Eop : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    (m₁ : GA E r) (f : Sm E a),
    (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) ∧
      ∀ (τ : E →+* ℂ) (p p' : Fin (a - r)) (ψ : Sm E (a - r)),
        ψ.1 = (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) →
        (Eop τ p p' ψ).1 = fun m₂ : GA E (a - r) =>
          (Eop τ (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) f).1
            (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  intro E _ _ _ a r hr m₁ f
  refine ⟨slice_mem_Sm hr m₁ f, fun τ p p' ψ hψ => funext fun m₂ => ?_⟩
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, lieS_slice hr m₁ f p p' ψ hψ]

end GlobalTheory.LeviSliceGA

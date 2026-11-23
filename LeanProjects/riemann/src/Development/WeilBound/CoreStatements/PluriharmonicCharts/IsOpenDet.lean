import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.c_bm_exists_period

section Hol
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def HolM (s : Set X) (A : X → Matrix I J ℂ) : Prop := ∀ a b, DifferentiableOn ℂ (fun x => A x a b) s

theorem HolM.const (s : Set X) (A : Matrix I J ℂ) : HolM s fun _ => A := fun _ _ => differentiableOn_const _

theorem HolM.mono {s t : Set X} {A : X → Matrix I J ℂ} (h : HolM s A) (ht : t ⊆ s) : HolM t A :=
  fun a b => (h a b).mono ht

theorem HolM.mul {s : Set X} {A : X → Matrix I J ℂ} {B : X → Matrix J K ℂ} (hA : HolM s A) (hB : HolM s B) :
    HolM s fun x => A x * B x := fun a b => by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun k _ => (hA a k).mul (hB k b)

theorem HolM.det [DecidableEq I] {s : Set X} {A : X → Matrix I I ℂ} (hA : HolM s A) :
    DifferentiableOn ℂ (fun x => (A x).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply DifferentiableOn.fun_sum
  intro σ _
  refine (differentiableOn_const _).mul ?_
  have key : ∀ t : Finset I, DifferentiableOn ℂ (fun x => ∏ i ∈ t, A x (σ i) i) s := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simp only [Finset.prod_empty]
      exact differentiableOn_const _
    · intro j t hj ih
      simp only [Finset.prod_insert hj]
      exact (hA (σ j) j).mul ih
  exact key Finset.univ

theorem HolM.inv [DecidableEq I] {s : Set X} {A : X → Matrix I I ℂ} (hA : HolM s A) (hd : ∀ x ∈ s, (A x).det ≠ 0) :
    HolM s fun x => (A x)⁻¹ := by
  intro a b
  have hu : HolM s fun x => (A x).updateRow b (Pi.single a 1) := by
    intro i k
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact differentiableOn_const _
    · exact hA i k
  simp only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hA.det.inv hd).mul hu.det

theorem HolM.isOpen_det [DecidableEq I] {s : Set X} {A : X → Matrix I I ℂ} (hA : HolM s A) (hs : IsOpen s) :
    IsOpen {x ∈ s | (A x).det ≠ 0} :=
  hA.det.continuousOn.isOpen_inter_preimage hs isOpen_ne

noncomputable def dM (A : X → Matrix I J ℂ) (u v : X) : Matrix I J ℂ :=
  Matrix.of fun a b => fderiv ℂ (fun x => A x a b) u v

theorem dM_mul {s : Set X} {A : X → Matrix I J ℂ} {B : X → Matrix J K ℂ} (hA : HolM s A) (hB : HolM s B) {u : X}
    (hu : s ∈ nhds u) (v : X) : dM (fun x => A x * B x) u v = dM A u v * B u + A u * dM B u v := by
  have hd : ∀ a b, DifferentiableAt ℂ (fun x => A x a b) u := fun a b => (hA a b).differentiableAt hu
  have he : ∀ a b, DifferentiableAt ℂ (fun x => B x a b) u := fun a b => (hB a b).differentiableAt hu
  ext a c
  simp only [dM, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  have key : HasFDerivAt (fun x => ∑ j, A x a j * B x j c)
      (∑ j, (A u a j • fderiv ℂ (fun x => B x j c) u + B u j c • fderiv ℂ (fun x => A x a j) u)) u :=
    HasFDerivAt.fun_sum fun j _ => (hd a j).hasFDerivAt.mul (he j c).hasFDerivAt
  rw [key.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring

theorem dM_const {A : X → Matrix I J ℂ} {C : Matrix I J ℂ} {u : X} (h : ∀ᶠ x in nhds u, A x = C) (v : X) :
    dM A u v = 0 := by
  ext a b
  simp only [dM, Matrix.of_apply, Matrix.zero_apply]
  have he : (fun x => A x a b) =ᶠ[nhds u] fun _ => C a b := h.mono fun x hx => by simp [hx]
  rw [he.fderiv_eq]
  simp

end Hol

end PositivityTheory.Xgp.c_bm_exists_period

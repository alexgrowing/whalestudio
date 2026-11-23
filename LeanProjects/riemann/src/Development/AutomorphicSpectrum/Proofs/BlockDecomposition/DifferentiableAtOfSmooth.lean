import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_fderiv_field {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem fderiv_field_bracket {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A B : E →L[ℝ] E)
    {g : E} (hg : g ∈ U) :
    fderiv ℝ (fun y => fderiv ℝ f y (B y)) g (A g) - fderiv ℝ (fun y => fderiv ℝ f y (A y)) g (B g) =
      fderiv ℝ f g (B (A g) - A (B g)) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) g :=
    ((h1.contDiffAt (hU.mem_nhds hg)).differentiableAt (by simp))
  have hs : IsSymmSndFDerivAt ℝ f g :=
    (hf.contDiffAt (hU.mem_nhds hg)).isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)
  have hA := (h2.hasFDerivAt.clm_apply A.hasFDerivAt).fderiv
  have hB := (h2.hasFDerivAt.clm_apply B.hasFDerivAt).fderiv
  rw [hA, hB]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_sub]
  rw [hs.eq (A g) (B g)]
  abel

theorem fderiv_add_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f + h) g v = fderiv ℝ f g v + fderiv ℝ h g v := by
  rw [fderiv_add hf hh]; rfl

end General

theorem fderiv_csmul_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (c : ℂ) (v : E) :
    fderiv ℝ (c • f) g v = c • fderiv ℝ f g v := by
  rw [fderiv_const_smul (R := ℂ) hf c]; rfl

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

def mulL (x : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

@[simp] theorem mulR_apply (X g : Mat n) : mulR X g = g * X := rfl
@[simp] theorem mulL_apply (x g : Mat n) : mulL x g = x * g := rfl

theorem differentiableAt_of_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    DifferentiableAt ℝ f g :=
  ((hf.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by simp))

theorem Rd_contDiffOn (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_fderiv_field isOpen_GLs hf (mulR X)

theorem Rd_bracket (X Y : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g := by
  have := fderiv_field_bracket isOpen_GLs hf (mulR X) (mulR Y) hg
  have e : (mulR Y) ((mulR X) g) - (mulR X) ((mulR Y) g) = g * (X * Y - Y * X) := by
    show g * X * Y - g * Y * X = _
    simp [mul_sub, mul_assoc]
  exact this.trans (congrArg (fderiv ℝ f g) e)

theorem Rd_congr (X : Mat n) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) : Set.EqOn (Rd X f) (Rd X h) (GLs n) := by
  intro g hg
  have : f =ᶠ[nhds g] h := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) e
  simp [Rd, this.fderiv_eq]

theorem Rd_add_left (X Y : Mat n) (f : Mat n → V) : Rd (X + Y) f = Rd X f + Rd Y f := by
  funext g; simp [Rd, mul_add]

theorem Rd_smul_left (r : ℝ) (X : Mat n) (f : Mat n → V) : Rd (r • X) f = r • Rd X f := by
  funext g
  simp only [Rd, Pi.smul_apply, mul_smul_comm, map_smul]

theorem Rd_add {f h : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    Set.EqOn (Rd X (f + h)) (Rd X f + Rd X h) (GLs n) := by
  intro g hg
  exact fderiv_add_apply' (differentiableAt_of_smooth hf hg) (differentiableAt_of_smooth hh hg) _

theorem Rd_smul (c : ℂ) (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rd X (c • f)) (c • Rd X f) (GLs n) := by
  intro g hg
  exact fderiv_csmul_apply (differentiableAt_of_smooth hf hg) c _

def IBP : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → Cpt f →
    ∀ X, ∫ y : G n, Rd X f y.val ∂μ = 0

end GlobalTheory.CompanionTheory.RCalc

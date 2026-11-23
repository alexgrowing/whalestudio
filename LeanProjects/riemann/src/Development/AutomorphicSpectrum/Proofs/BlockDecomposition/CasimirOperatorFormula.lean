import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.Casimir

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact (isOpen_compl_singleton (x := (0 : ℂ))).preimage hc

theorem contDiff_mul_right (X : Mat n) : ContDiff ℝ ∞ (fun g : Mat n => g * X) :=
  ((LinearMap.mulRight ℝ X).toContinuousLinearMap).contDiff

theorem differentiableAt_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) {g : Mat n}
    (hg : g ∈ GLs n) : DifferentiableAt ℝ (Rd X f) g := by
  have h1 := hf.fderiv_of_isOpen (m := 1) isOpen_GLs (by norm_cast)
  have h2 : ContDiffOn ℝ 1 (Rd X f) (GLs n) :=
    h1.clm_apply ((contDiff_mul_right X).contDiffOn.of_le (by norm_cast))
  exact (h2.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by norm_num)

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  have : fderiv ℝ (0 : Mat n → V) g = 0 := by
    simpa using fderiv_const_apply (𝕜 := ℝ) (x := g) (0 : V)
  simp [Rd, this]

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c a : Fin n) (f : Mat n → V) : Epow s 1 c a f = Eu s c a f := by
  simp only [Epow]
  rw [Finset.sum_eq_single a]
  · simp
  · intro d _ hd
    simp [hd, Eu_zero]
  · simp

theorem Rd_comb (X : Mat n) (σ : ℂ) {u v : Mat n → V} {g : Mat n} (hu : DifferentiableAt ℝ u g)
    (hv : DifferentiableAt ℝ v g) :
    Rd X ((1 / 2 : ℂ) • (u + σ • v)) g = (1 / 2 : ℂ) • (Rd X u g + σ • Rd X v g) := by
  have hsv : DifferentiableAt ℝ (σ • v) g := hv.const_smul σ
  have h1 : fderiv ℝ ((1 / 2 : ℂ) • (u + σ • v)) g = (1 / 2 : ℂ) • fderiv ℝ (u + σ • v) g :=
    fderiv_const_smul (hu.add hsv) _
  have h2 : fderiv ℝ (u + σ • v) g = fderiv ℝ u g + fderiv ℝ (σ • v) g := fderiv_add hu hsv
  have h3 : fderiv ℝ (σ • v) g = σ • fderiv ℝ v g := fderiv_const_smul hv _
  show fderiv ℝ ((1 / 2 : ℂ) • (u + σ • v)) g (g * X) = _
  rw [h1, h2, h3]
  rfl

theorem comb_identity (P B C Q : V) :
    (2 : ℂ) • ((1 / 2 : ℂ) • ((1 / 2 : ℂ) • (P + (-Complex.I) • B) +
          (-Complex.I) • ((1 / 2 : ℂ) • (C + (-Complex.I) • Q))) +
        (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (P + Complex.I • B) +
          Complex.I • ((1 / 2 : ℂ) • (C + Complex.I • Q)))) = P - Q := by
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem Eu_Eu {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a c : Fin n) {g : Mat n}
    (hg : g ∈ GLs n) :
    Eu s a c (Eu s c a f) g =
      (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (Rd (Matrix.single a c 1) (Rd (Matrix.single c a 1) f) g +
            (if s then -Complex.I else Complex.I) •
              Rd (Matrix.single a c 1) (Rd (Matrix.single c a Complex.I) f) g) +
        (if s then -Complex.I else Complex.I) •
          ((1 / 2 : ℂ) • (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a 1) f) g +
            (if s then -Complex.I else Complex.I) •
              Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g))) := by
  have hu := differentiableAt_Rd hf (Matrix.single c a (1 : ℂ)) hg
  have hv := differentiableAt_Rd hf (Matrix.single c a Complex.I) hg
  have e := fun X : Mat n => Rd_comb X (if s then -Complex.I else Complex.I) hu hv
  show ((1 / 2 : ℂ) • (Rd (Matrix.single a c 1) (Eu s c a f) +
    (if s then -Complex.I else Complex.I) • Rd (Matrix.single a c Complex.I) (Eu s c a f))) g = _
  simp only [Pi.smul_apply, Pi.add_apply]
  have e' : ∀ X : Mat n, Rd X (Eu s c a f) g = _ := e
  rw [e', e']

theorem omFormula : OmFormula := by
  intro n V _ _ f hf g hg
  have hgel : ∀ s : Bool, gel s 2 f g = ∑ a, ∑ c, Eu s a c (Eu s c a f) g := by
    intro s
    simp only [gel, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : Epow s 2 a a f = ∑ c, Eu s a c (Epow s 1 c a f) := rfl
    simp only [h2, Finset.sum_apply, Epow_one]
  simp only [Om, Pi.smul_apply, Pi.add_apply, hgel]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Eu_Eu hf true a c hg, Eu_Eu hf false a c hg]
  have key := comb_identity (V := V)
    (Rd (Matrix.single a c 1) (Rd (Matrix.single c a 1) f) g)
    (Rd (Matrix.single a c 1) (Rd (Matrix.single c a Complex.I) f) g)
    (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a 1) f) g)
    (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g)
  simp only [↓reduceIte, Bool.false_eq_true]
  exact key

end GlobalTheory.CompanionTheory.Casimir

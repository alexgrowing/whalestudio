import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Conj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.Regular

section Polydisc

variable {n a : ℕ}

theorem norm_star_vec (z : Fin n → ℂ) : ‖star z‖ = ‖z‖ := by
  simp only [Pi.norm_def, Pi.star_apply]
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  simp [nnnorm_star]

theorem star_mem_ball {ρ : ℝ} {z : Fin n → ℂ} :
    star z ∈ Metric.ball (0 : Fin n → ℂ) ρ ↔ z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
  simp only [mem_ball_zero_iff, norm_star_vec]

theorem star_mem_punct {ρ : ℝ} {z : Fin n → ℂ} : star z ∈ punct n a ρ ↔ z ∈ punct n a ρ := by
  simp only [punct, Set.mem_setOf_eq, star_mem_ball, Pi.star_apply, ne_eq, star_eq_zero]

theorem star_mem_logCover (h : a ≤ n) {w : Fin n → ℂ} : star w ∈ logCover h ↔ w ∈ logCover h := by
  simp only [logCover, Set.mem_setOf_eq, Pi.star_apply, Complex.star_def, Complex.conj_re,
    RCLike.norm_conj, Complex.norm_conj]

theorem star_expCover (w : Fin n → ℂ) : star (expCover a w) = expCover a (star w) := by
  funext k
  simp only [expCover, Pi.star_apply]
  split_ifs
  · simp [Complex.exp_conj]
  · rfl

theorem star_real_smul (ρ : ℝ) (z : Fin n → ℂ) : star ((ρ : ℂ) • z) = (ρ : ℂ) • star z := by
  funext k
  simp

theorem differentiableOn_star_star {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F]
    [StarModule ℂ F] [ContinuousStar F] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] [ContinuousStar V] {f : V → F} {B : Set V} (hB : IsOpen B) (hs : ∀ z, star z ∈ B ↔ z ∈ B)
    (hf : DifferentiableOn ℂ f B) : DifferentiableOn ℂ (fun z => star (f (star z))) B := by
  intro z hz
  have h1 : DifferentiableAt ℂ f (star z) := hf.differentiableAt (hB.mem_nhds ((hs z).2 hz))
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

end Polydisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def conjPts {R : Type} [CommRing R] {n : ℕ} (ψ : (Fin n → ℂ) → (R →+* ℂ)) (z : Fin n → ℂ) : R →+* ℂ :=
  (starRingEnd ℂ).comp (ψ (star z))

theorem isHolPts_conjPts {R : Type} [CommRing R] {n : ℕ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} {ρ : ℝ}
    (h : IsHolPts (Metric.ball 0 ρ) ψ) : IsHolPts (Metric.ball 0 ρ) (conjPts ψ) :=
  ⟨Metric.isOpen_ball, fun r => differentiableOn_star_star (f := fun b => ψ b r) Metric.isOpen_ball
    (fun _ => star_mem_ball) (h.2 r)⟩

def chart {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) :
    BdryChart Xo ((starRingEnd ℂ).comp σ) n a where
  a_le := C.a_le
  R := C.R
  t := C.t
  g := C.g
  dim := C.dim
  M := C.M
  ψ := conjPts C.ψ
  hol := isHolPts_conjPts C.hol
  V := C.V
  j := C.j
  j_open := C.j_open
  k := C.k
  tV := C.tV
  m₁ := C.m₁
  m₂ := C.m₂
  pt z := spMap (starRingEnd ℂ) ≫ C.pt (star z)
  pt_eq z hz := by
    obtain ⟨h1, h2⟩ := C.pt_eq (star z) (star_mem_punct.2 hz)
    constructor
    · rw [Category.assoc, h1]
      exact (Spec.map_comp _ _).symm
    · rw [Category.assoc, h2]
      exact (Spec.map_comp _ _).symm

end GlobalTheory.CompanionTheory.Ar.Flat.Conj

import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def PolarisedAt {X : Scheme.{0}} (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) : Prop :=
  ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

open Classical in

def gramFn (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) (w : (Σ k, J k) → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  if h : ∃ (Γ : Matrix (Fin r) (Fin r) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
      CoordsAt 𝔐.ξ y z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z b Γ then h.choose else 0

def recentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (ρ : ℂ)⁻¹ * (t (π.symm i) - t₀ (π.symm i))

def periodGram {n a₀ g r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (u : Fin n → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => Real.pi * (U j u ⬝ᵥ L.H u *ᵥ star (U i u))

def IsFramePeriods (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) {P : Ideal (MRing J)} {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω) {a₀ g : ℕ}
    {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) ∧ LinearIndependent ℂ (fun k => U k 0) ∧
  (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧
  ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧
    InFrameDomain y cc f (χ.γ (recentre t₀ ρ π u)) ∧ (χ.γ (recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) ∧
    (u ∈ Flat.punct n a₀ 1 → ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (χ.γ (recentre t₀ ρ π u)) →
      𝔐.M.GramAt 𝔐.t.PP.L z b (periodGram L U u))

theorem recentre_uncentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    recentre t₀ ρ π (uncentre t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [recentre, uncentre, h]

theorem isOpen_punct (n a : ℕ) (ρ : ℝ) : IsOpen (Flat.punct n a ρ) := by
  have : Flat.punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | i.val < a → z i ≠ 0} := by
    ext z; simp [Flat.punct]
  rw [this]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : i.val < a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

theorem contDiff_uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uncentre t₀ ρ π) := by
  unfold uncentre
  exact contDiff_pi.2 fun i => contDiff_const.mul ((contDiff_apply ℝ ℂ (π.symm i)).sub contDiff_const)

theorem uncentre_mem_ball {n : ℕ} {t₀ t : Fin n → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n))
    (h : ‖t - t₀‖ < ρ) : uncentre t₀ ρ π t ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖t (π.symm i) - t₀ (π.symm i)‖ ≤ ‖t - t₀‖ := norm_le_pi_norm (t - t₀) (π.symm i)
  simp only [uncentre, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  rw [inv_mul_lt_iff₀ hρ]
  linarith

theorem uncentre_self {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : uncentre t ρ π t = 0 := by
  funext i
  simp [uncentre]

theorem recentre_zero {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : recentre t ρ π 0 = t := by
  funext i
  simp [recentre]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric

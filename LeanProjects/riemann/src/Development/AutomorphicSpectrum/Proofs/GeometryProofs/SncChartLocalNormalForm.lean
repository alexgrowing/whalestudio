import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartGeo

open Topology

theorem inFrameDomain_eventually {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (cc : (k : K) → J k) (f : Ω) {z : (Σ k, J k) → ℂ} (hz : InFrameDomain y cc f z) :
    ∀ᶠ w in 𝓝 z, InFrameDomain y cc f w := by
  obtain ⟨hc, v, ⟨d, g, h, hg, hh, hy, hgh, hhz, rfl⟩, hv⟩ := hz
  have hgz : MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    apply hv
    rw [h0, zero_div]
  have c1 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hgz
  have c2 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hhz
  have c3 : ∀ᶠ w : (Σ k, J k) → ℂ in 𝓝 z, ∀ k, w ⟨k, cc k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (continuous_apply _).continuousAt.eventually_ne (hc k)
  filter_upwards [c1, c2, c3] with w h1 h2 h3
  exact ⟨h3, _, ⟨d, g, h, hg, hh, hy, hgh, h2, rfl⟩, div_ne_zero h1 h2⟩

theorem exists_perm_prefix {n : ℕ} (A : Finset (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, ((π i : Fin n) : ℕ) < A.card ↔ i ∈ A := by
  classical
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  let e : {x // x ∈ A} ≃ {j : Fin n // (j : ℕ) < A.card} :=
    A.equivFin.trans (Fin.castLEOrderIso hle).toEquiv
  refine ⟨e.extendSubtype, fun i => ⟨fun h => ?_, fun h => e.extendSubtype_mem i h⟩⟩
  by_contra hi
  exact e.extendSubtype_not_mem i hi h

theorem recentre_apply {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) (i : Fin n) :
    HodgeMetric.recentre t₀ ρ π u i = t₀ i + (ρ : ℂ) * u (π i) := by
  simp [HodgeMetric.recentre]

theorem recentre_mem_ball {n : ℕ} {t₀ u : Fin n → ℂ} {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ρ ≤ ε) (π : Equiv.Perm (Fin n))
    (hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1) : HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball t₀ ε := by
  rw [mem_ball_iff_norm]
  refine lt_of_lt_of_le ?_ hε
  rw [pi_norm_lt_iff hρ]
  intro i
  have h1 : ‖u (π i)‖ < 1 :=
    lt_of_le_of_lt (norm_le_pi_norm u (π i)) (by simpa using hu)
  have h2 : (HodgeMetric.recentre t₀ ρ π u - t₀) i = (ρ : ℂ) * u (π i) := by
    simp [recentre_apply]
  rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  nlinarith

theorem exists_recentre_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (P : Ideal (MRing J)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (HodgeMetric.recentre t₀ ρ π u)) ∧ (χ.γ (HodgeMetric.recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) := by
  intro K _ J _ Ω _ y P n Bd χ t₀ cc f ht₀ hF
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < χ.a ∧ t₀ i = 0)
  have hA : ∀ i, i ∈ A ↔ (i : ℕ) < χ.a ∧ t₀ i = 0 := fun i => by simp [A]
  obtain ⟨π, hπ⟩ := exists_perm_prefix A
  have hγ : ContinuousAt χ.γ t₀ := (χ.analytic t₀ ht₀).continuousAt
  have e1 : ∀ᶠ t in 𝓝 t₀, InFrameDomain y cc f (χ.γ t) :=
    hγ.eventually (inFrameDomain_eventually y cc f hF)
  have e2 : ∀ᶠ t : Fin n → ℂ in 𝓝 t₀, ∀ i : Fin n, t₀ i ≠ 0 → t i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : t₀ i = 0
    · exact Filter.Eventually.of_forall fun t h => absurd hi h
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with t ht _ using ht
  have e3 : ∀ᶠ t in 𝓝 t₀, t ∈ Metric.ball (0 : Fin n → ℂ) 1 :=
    Metric.isOpen_ball.mem_nhds ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  refine ⟨A.card, π, min ε 1, hle, lt_min hε one_pos, min_le_right _ _, fun i hi => ?_, fun ρ hρ hρ₀ u hu => ?_⟩
  · have : π.symm i ∈ A := (hπ _).1 (by simpa using hi)
    exact (hA _).1 this
  · obtain ⟨hF', hne, hb⟩ := hball _ (recentre_mem_ball hρ (hρ₀.trans (min_le_left _ _)) π hu)
    refine ⟨hb, hF', ?_⟩
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    rw [χ.boundary _ hb]
    constructor
    · intro h
      refine ⟨by simpa using hu, fun j hj => fun h0 => h ?_⟩
      have hm : π.symm j ∈ A := (hπ _).1 (by simpa using hj)
      obtain ⟨h1, h2⟩ := (hA _).1 hm
      refine ⟨π.symm j, h1, ?_⟩
      rw [recentre_apply, h2]
      simp [h0]
    · rintro ⟨-, hu'⟩ ⟨i, hi, h0⟩
      by_cases hti : t₀ i = 0
      · have hm : i ∈ A := (hA i).2 ⟨hi, hti⟩
        have := hu' (π i) ((hπ i).2 hm)
        rw [recentre_apply, hti, zero_add] at h0
        exact (mul_ne_zero hρc this) h0
      · exact hne i hti h0

end GlobalTheory.CompanionTheory.Ar.ChartGeo

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicSections

open Topology

namespace GlobalTheory.SmoothPointFamily

open KaehlerDifferential

set_option backward.isDefEq.respectTransparency.types false in

theorem exists_basis_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S) (m : ℕ) (s : Fin m → S)
      (b : Module.Basis (Fin m) (Localization.Away g) Ω[Localization.Away g⁄R]),
      g ∉ p ∧ ∀ i, b i = D R (Localization.Away g) (algebraMap S _ (s i)) := by
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let e : (κ →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i : κ ↦ D R S (a i)
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] := map R R S (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] :=
    map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  obtain ⟨m, ⟨u⟩⟩ := Finite.exists_equiv_fin κ
  let b' : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R] :=
    .ofRepr (LinearEquiv.ofBijective eₜ' h).symm
  have hb' : ∀ i, b' i = D R (Localization.Away g) (algebraMap S _ (a i)) := fun i => by
    simp +zetaDelta [IsLocalizedModule.map_linearCombination]
  exact ⟨g, m, fun i => a (u.symm i), b'.reindex u, hg, fun i => by
    rw [Module.Basis.reindex_apply, hb']⟩

theorem exists_etale_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S) (m : ℕ) (s : Fin m → S), g ∉ p ∧
      (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away g))
        fun i => algebraMap S (Localization.Away g) (s i)).Etale := by
  obtain ⟨g, m, s, b, hg, hb⟩ := exists_basis_away (R := R) p
  refine ⟨g, m, s, hg, ?_⟩
  letI : Algebra (MvPolynomial (Fin m) R) (Localization.Away g) :=
    (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away g))
        fun i => algebraMap S (Localization.Away g) (s i)).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin m) R) (Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [RingHom.algebraMap_toAlgebra]
      simp
  haveI : Algebra.Smooth S (Localization.Away g) := Algebra.Smooth.of_isLocalization_Away g
  haveI : Algebra.Smooth R (Localization.Away g) := Algebra.Smooth.comp R S _
  refine GlobalTheory.EtaleCoordJacobian.etale_of_basis R (Localization.Away g) (Fin m) b fun i => ?_
  rw [hb, RingHom.algebraMap_toAlgebra]
  simp

theorem exists_finset_of_mem_nhds {A : Type} {x : A → ℂ} {U : Set (A → ℂ)} (hU : U ∈ 𝓝 x) :
    ∃ (S : Finset A) (ε : ℝ), 0 < ε ∧ ∀ y : A → ℂ, (∀ a ∈ S, ‖y a - x a‖ < ε) → y ∈ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hI⟩ := hU
  choose δ hδ hδt using fun a => Metric.mem_nhds_iff.1 (ht a)
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a ∈ I, ε < δ a :=
    (Filter.eventually_all_finset I).2 fun a _ =>
      nhdsWithin_le_nhds (gt_mem_nhds (hδ a))
  obtain ⟨ε, h2, h3⟩ := (h1.and self_mem_nhdsWithin).exists
  refine ⟨I, ε, h3, fun y hy => hI fun a ha => hδt a ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact (hy a ha).trans (h2 a ha)

theorem exists_holomorphic_family : ∀ (K A : Type) [Field K] [CharZero K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ), φ₀.comp (algebraMap K A) = σ → ∃ (m : ℕ) (s : Fin m → A) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (S : Finset A) (ε : ℝ), IsOpen B ∧ 0 < ε ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ ∧ ∀ i, φ b (s i) = b i) ∧ (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧ ∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (∀ a ∈ S, ‖ψ a - φ₀ a‖ < ε) → (fun i => ψ (s i)) ∈ B ∧ φ (fun i => ψ (s i)) = ψ := by
  intro K A _ _ _ _ _ σ φ₀ h₀
  haveI : (RingHom.ker φ₀).IsPrime := RingHom.ker_isPrime φ₀
  obtain ⟨g, m, s, hg, het⟩ := exists_etale_away (R := K) (RingHom.ker φ₀)
  have hg₀ : φ₀ g ≠ 0 := hg
  let R := Localization.Away g
  let ι : A →+* R := algebraMap A R
  let L : (ψ : A →+* ℂ) → ψ g ≠ 0 → (R →+* ℂ) := fun ψ h =>
    IsLocalization.Away.lift g (g := ψ) (isUnit_iff_ne_zero.2 h)
  have hL : ∀ ψ h a, L ψ h (ι a) = ψ a := fun ψ h a => IsLocalization.Away.lift_eq g _ a
  let P : MvPolynomial (Fin m) K →+* R := MvPolynomial.eval₂Hom (algebraMap K R) fun i => ι (s i)
  have hPC : ∀ k, P (MvPolynomial.C k) = ι (algebraMap K A k) := fun k => by
    simp only [P, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply K A R k
  have hPX : ∀ i, P (MvPolynomial.X i) = ι (s i) := fun i => by simp [P]
  have hLC : ∀ (ψ : A →+* ℂ) h, ψ.comp (algebraMap K A) = σ →
      ∀ k, L ψ h (P (MvPolynomial.C k)) = σ k := fun ψ h hψ k => by
    rw [hPC, hL ψ h, ← hψ]; rfl
  obtain ⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩ :=
    GlobalTheory.EtaleFamily.exists_holomorphic_sections 0 m K R P Set.univ (fun _ => σ) 0 (L φ₀ hg₀) het
      isOpen_univ trivial (fun a => differentiableOn_const _) (hLC φ₀ hg₀ h₀)
  choose k c hc using fun j => IsLocalization.Away.surj g (f j)
  have hval : ∀ ψ h j, L ψ h (f j) = ψ (c j) / ψ g ^ k j := fun ψ h j => by
    have := congrArg (L ψ h) (hc j)
    rw [map_mul, map_pow, hL ψ h, hL ψ h] at this
    rw [← this, mul_div_cancel_right₀ _ (pow_ne_zero _ h)]
  have hcont : ContinuousAt
      (fun y : A → ℂ => ((0 : Fin 0 → ℂ), fun j => y (c j) / y g ^ k j)) φ₀ :=
    continuousAt_const.prodMk (continuousAt_pi.2 fun j =>
      (continuous_apply (c j)).continuousAt.div ((continuous_apply g).pow _).continuousAt
        (pow_ne_zero _ hg₀))
  have hU : {y : A → ℂ | y g ≠ 0 ∧ ((0 : Fin 0 → ℂ), fun j => y (c j) / y g ^ k j) ∈ O} ∈
      𝓝 (φ₀ : A → ℂ) := by
    refine Filter.Eventually.and ((continuous_apply g).continuousAt.eventually_ne hg₀)
      (hcont (hO.mem_nhds ?_))
    simpa only [hval] using hO₀
  obtain ⟨S, ε, hε, hS⟩ := exists_finset_of_mem_nhds hU
  have hin : Differentiable ℂ fun b : Fin m → ℂ => ((0 : Fin 0 → ℂ), b) :=
    (differentiable_const _).prodMk differentiable_id
  refine ⟨m, s, (fun b => ((0 : Fin 0 → ℂ), b)) ⁻¹' N, fun b => (τ (0, b)).comp ι, S, ε,
    hN.preimage hin.continuous, hε, fun b hb => ⟨RingHom.ext fun a => ?_, fun i => ?_⟩,
    fun a => (hd (ι a)).comp hin.differentiableOn fun _ h => h, fun ψ hψ hψS => ?_⟩
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← hPC]
    exact (hτ _ hb).2.1 a
  · rw [RingHom.comp_apply, ← hPX]
    exact (hτ _ hb).2.2 i
  · obtain ⟨h1, h2⟩ := hS ψ hψS
    obtain ⟨h3, h4⟩ := hrec 0 (L ψ h1) (hLC ψ h1 hψ) (by simpa only [hval] using h2)
    simp only [hPX, hL ψ h1] at h3 h4
    refine ⟨h3, RingHom.ext fun a => ?_⟩
    rw [RingHom.comp_apply, h4, hL ψ h1]

end GlobalTheory.SmoothPointFamily

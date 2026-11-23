import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGeneratorInvertConstantStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeTrivialModStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceOfNotMemGenFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentMatchesModelComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCmTypeLatticeComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeExteriorLatticeComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagWeightedDegreeSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianNormSectionValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointOverNumberFieldValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbedding
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlaceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDvrModelLatticeValuationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPrimeDividingUniformizerStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

theorem orderAt_of_unit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ Ω} {σ ϖ ϖ' : Ω}
    {M : ℕ} {a : ℤ} {p : Cpt ξ} (h : OrderAt L σ ϖ M a p) (hu : unitAt ξ p (ϖ / ϖ')) : OrderAt L σ ϖ' M a p := by
  obtain ⟨e, c, he, hL, hσ, hc⟩ := h
  refine ⟨e, c, he, hL, hσ, ?_⟩
  have h0 : ϖ ≠ 0 := fun h => hu.1 (by simp [h])
  have h1 : ϖ' ≠ 0 := fun h => hu.1 (by simp [h])
  have hz : ∀ n : ℤ, unitAt ξ p ((ϖ / ϖ') ^ n) := fun n => by
    cases n with
    | ofNat m => simpa using ZUnit.pow hu m
    | negSucc m => simpa using ZUnit.inv (ZUnit.pow hu (m + 1))
  have : c ^ M / ϖ' ^ a = c ^ M / ϖ ^ a * (ϖ / ϖ') ^ a := by
    rw [div_zpow]
    field_simp
  rw [this]
  exact ZUnit.mul hc (hz a)

theorem exists_orders (hZ : PropZ) {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {κ : Type} [Finite κ] {x : κ → Ω} {F' : Type} [Field F'] [NumberField F'] (ψ : F' →+* Ω)
    (hcl : ∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ)
    (hall : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ x) (hN : NormalCpt ξ) (L : Lat ξ Ω) (σ : Ω)
    (hL : L.IsVB 1 ⊤) (hg : ∀ p ∈ genFibre ℤ ξ, L.IsGenAt p σ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → TrivMod L (ℓ : Ω) ∨ NumTrivMod L (ℓ : Ω)) :
    ∃ r : HeightOneSpectrum (𝓞 F') →₀ ℚ, ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'),
      v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt ξ,
        (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → OrderAt L σ (ψ π) m k p := by
  classical
  have hchar : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hplace : ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
      ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) →
        OrderAt L σ (ψ π) M a p := by
    intro v π hπ
    obtain ⟨O, _, _, _, _, X', ξ', s, g, ϖ, hs, hϖ, hinj, hξs, hξg, hgen', hall', hϖπ, hrange, hreg, hsurj⟩ :=
      GlobalTheory.T.dvr_model_of_number_field_place X Ω ξ κ x F' ψ v π hall ht hN hπ
    obtain ⟨ℓ, hℓ, hℓv⟩ := GlobalTheory.T.exists_prime_dividing_uniformizer F' v π hπ
    obtain ⟨u, hu⟩ : ∃ u : O, algebraMap O Ω u = ψ ((ℓ : F') / π) :=
      (hrange _).2 ⟨_, hℓv, rfl⟩
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hcc : ConstClosed O Ω := by
      intro a ha
      obtain ⟨f, hf, hfa⟩ := ha
      have hlift : f.map (algebraMap O Ω) ∈ Polynomial.lifts ψ := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        rw [Polynomial.coeff_map]
        obtain ⟨b, -, hb⟩ := (hrange _).1 ⟨f.coeff n, rfl⟩
        exact ⟨b, hb⟩
      obtain ⟨f', hf'⟩ := (Polynomial.mem_lifts _).1 hlift
      have hne : f' ≠ 0 := by
        rintro rfl
        rw [Polynomial.map_zero] at hf'
        exact hf ((Polynomial.map_eq_zero_iff hinj).1 hf'.symm)
      obtain ⟨b, rfl⟩ := hcl a ⟨f', hne, by
        rw [← Polynomial.eval_map, hf', Polynomial.eval_map]
        exact hfa⟩
      by_cases hb : v.valuation F' b ≤ 1
      · obtain ⟨x₀, hx₀⟩ := (hrange (ψ b)).2 ⟨b, hb, rfl⟩
        exact ⟨x₀, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx₀.symm⟩
      · have hb0 : b ≠ 0 := by
          rintro rfl
          simp at hb
        have hb' : v.valuation F' b⁻¹ ≤ 1 := by
          rw [map_inv₀]
          exact inv_le_one_of_one_le₀ (le_of_not_ge hb)
        obtain ⟨y₀, hy₀⟩ := (hrange (ψ b⁻¹)).2 ⟨b⁻¹, hb', rfl⟩
        refine ⟨1, y₀, ?_, ?_⟩
        · rintro rfl
          rw [map_zero] at hy₀
          exact inv_ne_zero hb0 ((map_eq_zero ψ).1 hy₀.symm)
        · rw [hy₀, ← map_mul, mul_inv_cancel₀ hb0, map_one, map_one]
    have hℓu : (ℓ : Ω) = algebraMap O Ω (ϖ * u) := by
      rw [map_mul, hϖπ, hu, ← map_mul, mul_div_cancel₀ _ hπ0, map_natCast]
    obtain ⟨M, a, hM, h⟩ := @GlobalTheory.T.proper_dvr_model_lattice_valuation X X' Ω _ _ ξ ξ' g O _ _ _ _ s hs ϖ L σ ℓ u hZ hϖ hinj hξs hξg ht.gen hgen' hall'
      hN hcc hreg hL hg hℓu (hp ℓ hℓ)
    refine ⟨M, a, hM, fun p hv => ?_⟩
    have := h p (hsurj p hv)
    rwa [hϖπ] at this
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.T.finite_type_over_integers_model X Ω ξ κ x hall ht
  obtain ⟨n, hn, hgn⟩ := @GlobalTheory.T.lattice_generator_invert_constant X Ω _ ξ ℤ _ _ _ s _ hs1 hs2 hs3 (Int.cast_injective) ht.gen L Set.univ 1 σ
    one_ne_zero (fun _ _ => trivial) hL hg
  have hn' : ((n : F'))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F') ((n : F'))⁻¹
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F') => v.valuation_exists_uniformizer F'
  choose M a hM hord using fun v => hplace v (π v) (hπ v)
  let T := HeightOneSpectrum.Support (𝓞 F') ((n : F'))⁻¹
  let r₀ : HeightOneSpectrum (𝓞 F') → ℚ := fun v => if v ∈ T then (a v : ℚ) / M v else 0
  have hr₀ : (Function.support r₀).Finite := hfin.subset fun v hv => by
    by_contra h
    exact hv (if_neg h)
  refine ⟨Finsupp.ofSupportFinite r₀ hr₀, fun v π' hπ' => ?_⟩
  have hrv : (Finsupp.ofSupportFinite r₀ hr₀) v = r₀ v := rfl
  rw [hrv]
  by_cases hv : v ∈ T
  · have hMv : (M v : ℚ) ≠ 0 := by exact_mod_cast (hM v).ne'
    refine ⟨M v, a v, hM v, by simp only [r₀, if_pos hv]; field_simp, fun p hp => ?_⟩
    refine orderAt_of_unit (hord v p hp) ?_
    have h0 : π' ≠ 0 := by
      rintro rfl
      simp at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have h1 : π v ≠ 0 := by
      intro h
      have := hπ v
      rw [h] at this
      simp at this
      exact WithZero.exp_ne_zero this.symm
    have e1 : v.valuation F' (π v / π') = 1 := by
      rw [map_div₀, hπ v, hπ', div_self (WithZero.exp_ne_zero)]
    have e2 : v.valuation F' (π v / π')⁻¹ = 1 := by rw [map_inv₀, e1, inv_one]
    rw [← map_div₀]
    exact ⟨(map_ne_zero ψ).2 (div_ne_zero h1 h0), hp _ e1.le, by rw [← map_inv₀]; exact hp _ e2.le⟩
  · refine ⟨1, 0, one_pos, by simp only [r₀, if_neg hv]; simp, fun p hp => ?_⟩
    have h1 : v.valuation F' (n : F') ≤ 1 := by
      have := v.valuation_le_one (K := F') (n : 𝓞 F')
      simpa using this
    have h2 : v.valuation F' ((n : F'))⁻¹ ≤ 1 := not_lt.1 hv
    have hu : unitAt ξ p (algebraMap ℤ Ω n) := by
      have e : algebraMap ℤ Ω n = ψ (n : F') := by simp
      rw [e]
      exact ⟨(map_ne_zero ψ).2 (by exact_mod_cast hn), hp _ h1, by rw [← map_inv₀]; exact hp _ h2⟩
    have := hgn p hu
    exact orderAt_one_zero.2 this

theorem isCoeffAt_of_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V} {x : Cpt ξ}
    {d₁ d₂ : Ω} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (ea : a' = d₁ • a) (eb : b' = d₂ • b)
    (h : IsCoeffAt A B p q a' b' x 1) : IsCoeffAt A B p q a b x (d₁ / d₂)⁻¹ := by
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  rw [one_mul] at e
  subst e
  refine ⟨α * d₁, α * d₂, mul_ne_zero hα h₁, mul_ne_zero hα h₂, ?_, ?_, ?_⟩
  · rw [hA, ea, smul_smul]
  · rw [hB, eb, smul_smul]
  · field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralQuotientOfValuationSubringAboveDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueNormalOfProfiniteInvariantsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ResidueFixed

theorem residue_fixed_mem : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ x ∈ V, (∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → V.valuation (σ x - x) < 1) → ∃ r : R, V.valuation (x - algebraMap K Ω (algebraMap R K r)) < 1 := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV x hx hfix
  classical
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have h : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact h
  let φ : R →+* V := (algebraMap R Ω).codRestrict V.toSubring hRV

  have hmR : ∀ r ∈ maximalIdeal R, V.valuation (algebraMap R Ω r) < 1 := by
    intro r hr
    by_contra hlt
    have h1 : V.valuation (algebraMap R Ω r) = 1 :=
      le_antisymm (V.valuation_le_one (φ r)) (not_lt.1 hlt)
    have hu : IsUnit (φ r) := (V.valuation_eq_one_iff (φ r)).2 h1
    have hne : algebraMap R K r ≠ 0 := by
      intro h0
      rw [show algebraMap R Ω r = algebraMap K Ω (algebraMap R K r) from rfl, h0, map_zero, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω (algebraMap R K r)⁻¹ ∈ V
      obtain ⟨u, hu'⟩ := hu
      have : ((u⁻¹ : Vˣ) : V) * φ r = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Vˣ) : V)) : Ω) = algebraMap K Ω (algebraMap R K r)⁻¹ := by
        rw [map_inv₀]
        refine (eq_inv_of_mul_eq_one_left ?_)
        exact congrArg Subtype.val this
      rw [← h2]; exact SetLike.coe_mem _
    rw [hV] at hinv
    obtain ⟨r', hr'⟩ := hinv
    apply (mem_maximalIdeal r).1 hr
    refine isUnit_iff_exists_inv.2 ⟨r', IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr', map_one, mul_inv_cancel₀ hne]

  let B := integralClosure R Ω
  have hBV : ∀ b : B, (b : Ω) ∈ V := by
    intro b
    obtain ⟨p, hpm, hp⟩ := b.2
    have hint : IsIntegral V (b : Ω) := by
      refine ⟨p.map φ, hpm.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hp
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    rw [← hy]; exact y.2
  let ψ : B →+* V := (B.val : B →+* Ω).codRestrict V.toSubring hBV
  let Q : Ideal B := (maximalIdeal V).comap ψ
  have hQ : ∀ b : B, b ∈ Q ↔ V.valuation (b : Ω) < 1 := fun b => V.valuation_lt_one_iff (ψ b)
  let G := Ω ≃ₐ[K] Ω
  have hc : SMulCommClass G R Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have : ContinuousSMul G B := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant R B G := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral R k := by
      have h2 : IsIntegral R (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff (algebraMap K Ω).injective).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hQP : Q.LiesOver (maximalIdeal R) := by
    constructor
    refine le_antisymm (fun r hr => ?_) (IsLocalRing.le_maximalIdeal ?_)
    · change algebraMap R B r ∈ Q
      rw [hQ]; exact hmR r hr
    · intro h1
      have h : (1 : R) ∈ Q.comap (algebraMap R B) := by
        change (1 : R) ∈ Q.under R
        rw [h1]; exact Submodule.mem_top
      rw [Ideal.mem_comap, map_one, hQ] at h
      simp at h
  have hQmax : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (maximalIdeal R)
  letI := Ideal.Quotient.field (maximalIdeal R)
  letI := Ideal.Quotient.field Q
  haveI hN : Normal (R ⧸ maximalIdeal R) (B ⧸ Q) := GlobalTheory.T.residue_normal_of_profinite_invariants G (maximalIdeal R) Q
  haveI : PerfectField (R ⧸ maximalIdeal R) := ‹PerfectField (ResidueField R)›
  haveI : IsGalois (R ⧸ maximalIdeal R) (B ⧸ Q) := {}

  have hBle : ∀ b : B, V.valuation (b : Ω) ≤ 1 := fun b => V.valuation_le_one (ψ b)

  have hsub : ∀ g ∈ MulAction.stabilizer G Q, ∀ y ∈ V, g y ∈ V := by
    intro g hg y hy
    obtain ⟨a, s, ha, hs, hsv, hys⟩ := GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr R K Ω V hV y hy
    let a' : B := ⟨a, ha⟩
    let s' : B := ⟨s, hs⟩
    have hs'Q : s' ∉ Q := by rw [hQ]; exact fun h => (ne_of_lt h) hsv
    have hgs : g • s' ∉ Q := by
      intro h
      apply hs'Q
      have h' : g • s' ∈ g • Q := by rw [MulAction.mem_stabilizer_iff.1 hg]; exact h
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul] at h'
      exact h'
    have hgsv : V.valuation (g s) = 1 := by
      rw [hQ] at hgs
      exact le_antisymm (hBle (g • s')) (not_lt.1 hgs)
    have hga : V.valuation (g a) ≤ 1 := hBle (g • a')
    apply V.mem_of_valuation_le_one
    have : g y * g s = g a := by rw [← map_mul, hys]
    rw [← this, map_mul, hgsv, _root_.mul_one] at hga
    exact hga
  have hstabV : ∀ g ∈ MulAction.stabilizer G Q, g • V = V := by
    intro g hg
    ext z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hz
      have := hsub g hg _ hz
      have e : g (g⁻¹ • z) = z := smul_inv_smul g z
      rwa [e] at this
    · intro hz
      exact hsub g⁻¹ (inv_mem hg) z hz

  obtain ⟨a, s, ha, hs, hsv, hxs⟩ := GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr R K Ω V hV x hx
  let a' : B := ⟨a, ha⟩
  let s' : B := ⟨s, hs⟩
  have hs'Q : s' ∉ Q := by rw [hQ]; exact fun h => (ne_of_lt h) hsv
  have hsne : Ideal.Quotient.mk Q s' ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  let ξ : B ⧸ Q := Ideal.Quotient.mk Q a' / Ideal.Quotient.mk Q s'
  have hξ : ∀ τ : (B ⧸ Q) ≃ₐ[R ⧸ maximalIdeal R] (B ⧸ Q), τ ξ = ξ := by
    intro τ
    obtain ⟨⟨σ, hσQ⟩, hστ⟩ :=
      Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) (maximalIdeal R) Q τ
    have hlt := hfix σ (hstabV σ hσQ)
    have hσs : σ • s' ∉ Q := by
      intro h
      apply hs'Q
      have h' : σ • s' ∈ σ • Q := by rw [MulAction.mem_stabilizer_iff.1 hσQ]; exact h
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul] at h'
      exact h'
    have hσsv : V.valuation (σ s) = 1 := by
      have h := hσs
      rw [hQ] at h
      exact le_antisymm (hBle (σ • s')) (not_lt.1 h)
    have hσs0 : Ideal.Quotient.mk Q (σ • s') ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hστ]
    simp only [ξ, map_div₀, Ideal.Quotient.stabilizerHom_apply]
    change Ideal.Quotient.mk Q (σ • a') / Ideal.Quotient.mk Q (σ • s') = _
    rw [div_eq_div_iff hσs0 hsne, ← map_mul, ← map_mul, Ideal.Quotient.eq, hQ]
    have e : ((σ • a' * s' - a' * σ • s' : B) : Ω) = (σ x - x) * s * σ s := by
      change σ a * s - a * σ s = _
      rw [← hxs, map_mul]; ring
    rw [e, map_mul, map_mul, hsv, hσsv, _root_.mul_one, _root_.mul_one]
    exact hlt
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := R ⧸ maximalIdeal R) ξ).2 hξ
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨r, ?_⟩
  have h1 : Ideal.Quotient.mk Q (algebraMap R B r) = ξ := hc
  have h2 : Ideal.Quotient.mk Q (algebraMap R B r * s') = Ideal.Quotient.mk Q a' := by
    rw [map_mul, h1, div_mul_cancel₀ _ hsne]
  rw [Ideal.Quotient.eq, hQ] at h2
  have e : ((algebraMap R B r * s' - a' : B) : Ω) = (algebraMap K Ω (algebraMap R K r) - x) * s := by
    change algebraMap K Ω (algebraMap R K r) * s - a = _
    rw [← hxs]; ring
  rw [e, map_mul, hsv, _root_.mul_one, Valuation.map_sub_swap] at h2
  exact h2

end GlobalTheory.ResidueFixed

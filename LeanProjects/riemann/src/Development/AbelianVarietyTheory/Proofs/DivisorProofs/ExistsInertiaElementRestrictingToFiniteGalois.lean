import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnValuationRings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfForall
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaRestrict

variable {Ω : Type} [Field Ω]

theorem lt_one_iff_of_sub_lt (V : ValuationSubring Ω) {x y : Ω} (h : V.valuation (x - y) < 1) :
    V.valuation x < 1 ↔ V.valuation y < 1 := by
  constructor
  · intro hx
    have : y = x - (x - y) := by ring
    rw [this]
    exact Valuation.map_sub_lt _ hx h
  · intro hy
    have : x = y + (x - y) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hy h

theorem comap_valuation_lt_one_iff {L : Type} [Field L] (f : L →+* Ω) (V : ValuationSubring Ω) (z : L) :
    (V.comap f).valuation z < 1 ↔ V.valuation (f z) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f f.injective]

theorem valuation_eq_one {V : ValuationSubring Ω} {s : Ω} (hs : s ∈ V) (h : ¬ V.valuation s < 1) :
    V.valuation s = 1 :=
  le_antisymm ((V.valuation_le_one_iff s).2 hs) (not_lt.1 h)

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj IntermediateField

theorem exists_den_integral (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsSeparable K Ω] (V : ValuationSubring Ω) (hR : ∀ r : R, algebraMap R Ω r ∈ V) {x : Ω}
    (hx : x ∈ V) :
    ∃ s t : Ω, IsIntegral R s ∧ IsIntegral R t ∧ V.valuation s = 1 ∧ s * x = t := by
  let M : IntermediateField K Ω := K⟮x⟯
  haveI : FiniteDimensional K M := adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral K x)
  haveI : Algebra.IsSeparable K M := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
  haveI : IsDedekindDomain (integralClosure R M) := integralClosure.isDedekindDomain R K M
  haveI : IsFractionRing (integralClosure R M) M := integralClosure.isFractionRing_of_finite_extension K M
  haveI : IsScalarTower R M Ω := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K Ω, IsScalarTower.algebraMap_apply R K M]
    rfl
  let A := V.comap (algebraMap M Ω)
  have hint : ∀ s : integralClosure R M, IsIntegral R ((s : M) : Ω) := fun s =>
    (s.2).map (IsScalarTower.toAlgHom R M Ω)
  have hS : ∀ s : integralClosure R M, algebraMap (integralClosure R M) M s ∈ A := fun s =>
    mem_of_isIntegral V hR (hint s)
  obtain ⟨s, t, hs, e⟩ := exists_den (integralClosure R M) A hS (x := ⟨x, mem_adjoin_simple_self K x⟩) hx
  refine ⟨((s : M) : Ω), ((t : M) : Ω), hint s, hint t, valuation_eq_one (hS s) ?_, ?_⟩
  · intro h
    have h2 : A.valuation (algebraMap (integralClosure R M) M s) < 1 :=
      (comap_valuation_lt_one_iff (algebraMap M Ω) V _).2 h
    rw [hs] at h2
    exact lt_irrefl _ h2
  · have := congrArg (algebraMap M Ω) e
    simpa using this

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj

section crit

variable (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsSeparable K Ω] (V : ValuationSubring Ω) (hR : ∀ r : R, algebraMap R Ω r ∈ V)

include hR in
theorem map_mem_of_lt_one_iff (g : Ω ≃ₐ[K] Ω)
    (hg : ∀ b : Ω, IsIntegral R b → (V.valuation (g b) < 1 ↔ V.valuation b < 1)) {x : Ω} (hx : x ∈ V) :
    g x ∈ V := by
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den_integral R K Ω V hR hx
  have hgs : V.valuation (g s) = 1 :=
    valuation_eq_one (mem_of_isIntegral V hR (hs.map (g.restrictScalars R))) (by
      rw [hg s hs, hs1]; exact lt_irrefl 1)
  have e' : g s * g x = g t := by rw [← map_mul, e]
  have := congrArg V.valuation e'
  rw [Valuation.map_mul, hgs, _root_.one_mul] at this
  rw [← V.valuation_le_one_iff, this, V.valuation_le_one_iff]
  exact mem_of_isIntegral V hR (ht.map (g.restrictScalars R))

include hR in

theorem smul_eq_of_lt_one_iff (g : Ω ≃ₐ[K] Ω)
    (hg : ∀ b : Ω, IsIntegral R b → (V.valuation (g b) < 1 ↔ V.valuation b < 1)) : g • V = V := by
  have hgi : ∀ y : Ω, g (g⁻¹ y) = y := fun y => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hg' : ∀ b : Ω, IsIntegral R b → (V.valuation (g⁻¹ b) < 1 ↔ V.valuation b < 1) := by
    intro b hb
    have := hg (g⁻¹ b) (hb.map ((g⁻¹ : Ω ≃ₐ[K] Ω).restrictScalars R))
    rw [hgi] at this
    exact this.symm
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  constructor
  · intro h
    have := map_mem_of_lt_one_iff R K Ω V hR g hg h
    rwa [hgi] at this
  · intro h
    exact map_mem_of_lt_one_iff R K Ω V hR g⁻¹ hg' h

include hR in

theorem mem_inertia_of_sub_lt_one (g : Ω ≃ₐ[K] Ω)
    (h : ∀ b : Ω, IsIntegral R b → V.valuation (g b - b) < 1) : g ∈ inertia K V := by
  have hg : g • V = V := smul_eq_of_lt_one_iff R K Ω V hR g fun b hb => lt_one_iff_of_sub_lt V (h b hb)
  rw [mem_inertia_iff]
  refine ⟨hg, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den_integral R K Ω V hR hx
  have hgs : V.valuation (g s) = 1 :=
    valuation_eq_one (mem_of_isIntegral V hR (hs.map (g.restrictScalars R))) (by
      rw [lt_one_iff_of_sub_lt V (h s hs), hs1]; exact lt_irrefl 1)
  have key : g s * (g x - x) = (g t - t) - x * (g s - s) := by
    rw [← e, map_mul]; ring
  have := congrArg V.valuation key
  rw [Valuation.map_mul, hgs, _root_.one_mul] at this
  rw [this]
  refine Valuation.map_sub_lt _ (h t ht) ?_
  rw [Valuation.map_mul]
  calc V.valuation x * V.valuation (g s - s) ≤ 1 * V.valuation (g s - s) :=
        mul_le_mul_left ((V.valuation_le_one_iff x).2 hx) _
    _ < 1 := by rw [_root_.one_mul]; exact h s hs

end crit

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj

theorem exists_mem_inertia_eq_on : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] (τ : L ≃ₐ[K] L), τ ∈ inertia K (V.comap (algebraMap L Ω)) →
    ∃ σ ∈ inertia K V, ∀ y : L, σ (y : Ω) = (τ y : Ω) := by
  first
  | exact @_root_.GlobalTheory.IntegralFractionLift.inertia_surjective
  | exact _root_.GlobalTheory.IntegralFractionLift.inertia_surjective
  | (apply _root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralFractionLift.inertia_surjective ..)

end GlobalTheory.InertiaRestrict

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetSpan

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem ord_nonneg_of_int (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (x : R) :
    0 ≤ ord_vw R (algebraMap R (FractionRing R) x) := by
  unfold ord_vw
  by_cases hx : x = 0
  · subst hx; simp
  · have h0 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) (algebraMap R (FractionRing R) x) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hx
    have h1 := (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one (K := FractionRing R) x
    have := (WithZero.log_le_log h0 one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    omega

theorem ord_le (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ) (D t u : R)
    (h : D ^ n = t * u) (hD : D ≠ 0) :
    ord_vw R (algebraMap R (FractionRing R) u) ≤ n * ord_vw R (algebraMap R (FractionRing R) D) := by
  unfold ord_vw
  set v := (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
  have inj := IsFractionRing.injective R (FractionRing R)
  have hDn : D ^ n ≠ 0 := pow_ne_zero _ hD
  have hu : u ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact hDn h
  have ne : ∀ y : R, y ≠ 0 → v (algebraMap R (FractionRing R) y) ≠ 0 := fun y hy => by
    rw [Valuation.ne_zero_iff]; exact (map_ne_zero_iff _ inj).2 hy
  have e1 : v (algebraMap R (FractionRing R) D) ^ n = v (algebraMap R (FractionRing R) t) * v (algebraMap R (FractionRing R) u) := by
    rw [← map_pow, ← map_pow, h, map_mul, map_mul]
  have e2 : v (algebraMap R (FractionRing R) D) ^ n ≤ v (algebraMap R (FractionRing R) u) := by
    rw [e1]
    exact mul_le_of_le_one_left' ((IsDiscreteValuationRing.maximalIdeal R).valuation_le_one (K := FractionRing R) t)
  have e3 := (WithZero.log_le_log (pow_ne_zero _ (ne D hD)) (ne u hu)).2 e2
  rw [WithZero.log_pow, nsmul_eq_mul] at e3
  linarith

theorem wedge_eq_smul_gen_val_le : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (L : Type) [AddCommGroup L] [Module R L]
    [Module.Free R L] [Module.Finite R L] (n : ℕ), Module.finrank R L = n →
    ∀ (e : Fin n → (L →ₗ[R] R)) (D : R), D ≠ 0 → (∀ ω : L →ₗ[R] R, D • ω ∈ Submodule.span R (Set.range e)) →
    ∀ (l : ℕ), ∃ (δ₀ : L [⋀^Fin n]→ₗ[R] R) (u₀ : R), Submodule.span R {δ₀} = ⊤ ∧
      Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) = u₀ • δ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        n • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  intro R _ _ _ L _ _ _ _ n hn e D hD hspan l
  classical
  let b := Module.finBasisOfFinrankEq R L hn
  refine ⟨b.det, Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) b, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro f _
    rw [AlternatingMap.eq_smul_basis_det b f]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact AlternatingMap.eq_smul_basis_det b _
  · set u := Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) b with hu_def
    choose t ht using fun k => (Submodule.mem_span_range_iff_exists_fun R).1 (hspan (b.coord k))
    let E : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => e i (b j)
    have hu : u = E.det := by
      rw [← Matrix.det_transpose]
      rfl
    have hm : Matrix.of t * E = D • (1 : Matrix (Fin n) (Fin n) R) := by
      ext k j
      have := congrArg (fun f : L →ₗ[R] R => f (b j)) (ht k)
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply,
        Module.Basis.repr_self] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, E, Matrix.smul_apply, Matrix.one_apply, this, smul_eq_mul,
        Finsupp.single_apply]
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj, Ne.symm hkj]
    have hkey : D ^ n = (Matrix.of t).det * u := by
      rw [hu, ← Matrix.det_mul, hm, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, _root_.mul_one]
    have hord := ord_le R n D _ u hkey hD
    have hu0 : u ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hkey; exact pow_ne_zero n hD hkey
    have inj := IsFractionRing.injective R (FractionRing R)
    have hc : (0 : ℚ) ≤ (ord_vw R ((l : ℕ) : FractionRing R) : ℚ) := by
      rw [← map_natCast (algebraMap R (FractionRing R))]
      exact_mod_cast ord_nonneg_of_int R (l : R)
    unfold val_vp
    rw [if_neg ((map_ne_zero_iff _ inj).2 hu0), if_neg ((map_ne_zero_iff _ inj).2 hD), ← WithTop.coe_nsmul,
      WithTop.coe_le_coe, nsmul_eq_mul, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hc
    exact_mod_cast hord

end GlobalTheory.DetSpan

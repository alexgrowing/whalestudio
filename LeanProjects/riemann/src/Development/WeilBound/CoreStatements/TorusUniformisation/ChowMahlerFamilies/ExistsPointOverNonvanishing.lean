import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.PointOverExistence

theorem exists_algHom (F R : Type) [Field F] [CommRing R] [Nontrivial R] [Algebra F R]
    [Algebra.FiniteType F R] [Algebra F ℂ] : Nonempty (R →ₐ[F] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (R ⧸ m)
  exact ⟨(IsAlgClosed.lift : (R ⧸ m) →ₐ[F] ℂ).comp (Ideal.Quotient.mkₐ F m)⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem scale {S : Type} [CommRing S] (t : K → S) (u : (Σ k, ι k) → S) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) :
    aeval (fun p : Σ k, ι k => t p.1 * u p) g = (∏ k, t k ^ d k) * aeval u g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h : ∏ p : Σ k, ι k, t p.1 ^ m p = ∏ k, t k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hg m hm k]
    exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i => m ⟨k, i⟩) (t k)
  simp only [mul_pow, Finset.prod_mul_distrib, h]
  ring

theorem map_aeval' {S T : Type} [CommRing S] [CommRing T] (j : S →+* T) (u : (Σ k, ι k) → S)
    (g : MRing ι) : j (aeval u g) = aeval (fun p => j (u p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, aeval_X]

theorem evC_eq (z : (Σ k, ι k) → ℂ) (g : MRing ι) : evC z g = aeval z g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq => simp only [evC, map_add] at *; rw [hp, hq]
  | mul_X p i hp => simp only [evC, map_mul, map_X, eval_X, aeval_X] at *; rw [hp]

variable {Ω : Type} [Field Ω]

theorem cone_eq (y : (Σ k, ι k) → Ω) (g : MRing ι) : mConeMap y g =
    @aeval ℤ (MvPolynomial K Ω) _ _ _ (Ring.toIntAlgebra _) (fun p : Σ k, ι k => X p.1 * C (y p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eq_intCast, map_intCast]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, mConeMap, aeval_X, mul_comm (C _)]

theorem aeval_ne_zero {y : (Σ k, ι k) → Ω} {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hn : g ∉ mCoordIdeal y) : aeval y g ≠ 0 := by
  intro h0
  apply hn
  have h := scale (S := MvPolynomial K Ω) (fun k => X k) (fun p => C (y p)) hg
  rw [← map_aeval' (C : Ω →+* MvPolynomial K Ω) y g, h0, map_zero, mul_zero] at h
  show mConeMap y g = 0
  rw [cone_eq, h]

theorem aeval_eq_zero {y : (Σ k, ι k) → Ω} (t : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p : Σ k, ι k => t p.1 * y p) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have h := map_aeval' (eval t : MvPolynomial K Ω →+* Ω)
    (fun p : Σ k, ι k => X p.1 * C (y p)) f
  rw [← cone_eq, h0, map_zero] at h
  rw [h]
  simp only [map_mul, eval_C, eval_X]

end PositivityTheory.Xgn.PointOverExistence

open PositivityTheory.Xgn.PointOverExistence in
theorem PositivityTheory.Xgn.exists_point_over_nonvanishing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (g : MRing ι) (d : K → ℕ), OverInt y φ → IsMultiHomog g d → g ∉ mCoordIdeal y → ∃ z, PtOver y φ σ z ∧ evC z g ≠ 0 := by
  intro K _ ι _ Ω _ F _ _ y φ σ g d hO hg hn
  choose c hc using hO.1
  letI : Algebra F Ω := φ.toAlgebra
  letI : Algebra F ℂ := σ.toAlgebra
  let t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  let w : (Σ k, ι k) → Ω := fun p => t p.1 * y p
  have hγ : aeval w g ≠ 0 := by
    rw [scale t y hg]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k)))
      (aeval_ne_zero hg hn)
  let A : Subalgebra F Ω := Algebra.adjoin F (insert (aeval w g)⁻¹ (Set.range w))
  haveI : Algebra.FiniteType F A :=
    Algebra.FiniteType.adjoin_of_finite ((Set.finite_range w).insert _)
  obtain ⟨ψ⟩ := exists_algHom F A
  let wA : (Σ k, ι k) → A := fun p => ⟨w p, Algebra.subset_adjoin (Or.inr ⟨p, rfl⟩)⟩
  let δ : A := ⟨(aeval w g)⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩
  have hco : ∀ f : MRing ι, ((aeval wA f : A) : Ω) = aeval w f := fun f =>
    map_aeval' (A.val : A →+* Ω) wA f
  have hev : ∀ f : MRing ι, evC (fun p => ψ (wA p)) f = ψ (aeval wA f) := fun f => by
    rw [evC_eq]
    exact (map_aeval' (ψ : A →+* ℂ) wA f).symm
  refine ⟨fun p => ψ (wA p), ⟨⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩, fun a e f h hf hh H => ?_⟩, ?_⟩
  · have : wA ⟨k, c k⟩ = 1 := Subtype.ext (inv_mul_cancel₀ (hc k))
    simp only [this, map_one]
    exact one_ne_zero
  · have : aeval wA f = 0 := Subtype.ext ((hco f).trans (aeval_eq_zero t hf))
    exact (hev f).trans (by rw [this, map_zero])
  · have : aeval wA f = algebraMap F A a * aeval wA h := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hco, hco, scale t y hf, scale t y hh, H]
      show _ = φ a * _
      ring
    rw [hev, hev, this, map_mul, ψ.commutes]
    rfl
  · have : aeval wA g * δ = 1 := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hco]
      exact mul_inv_cancel₀ hγ
    rw [hev]
    exact left_ne_zero_of_mul_eq_one (b := ψ δ) (by rw [← map_mul, this, map_one])

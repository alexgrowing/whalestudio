import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EvalEqZeroOfMemVanIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSetOfHilbertFunctionsFibresStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FormsFamily

theorem exists_const_near {R α : Type} [CommRing R] [PartialOrder α] {P : Set (Ideal R)} (hP : DenseP P)
    (r : ∀ (K : Type) [Field K], (R →+* K) → α) (ρ : α) (g : R)
    (hsc : ∀ (K : Type) [Field K] (x : R →+* K), ∃ f : R, x f ≠ 0 ∧
      ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → r L y ≤ r K x)
    (hρ : ∀ q ∈ P, g ∉ q → ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ r K x = ρ)
    (K : Type) [Field K] (x : R →+* K) (hg : x g ≠ 0) (hx : r K x = ρ) :
    ∃ f : R, x f ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → r L y = ρ := by
  obtain ⟨f, hf, h⟩ := hsc K x
  refine ⟨f * g, by rw [map_mul]; exact mul_ne_zero hf hg, fun L _ y hy => ?_⟩
  rw [map_mul] at hy
  refine le_antisymm (hx ▸ h L y (left_ne_zero_of_mul hy)) ?_
  obtain ⟨f', hf', h'⟩ := hsc L y
  have h0 : f' * g ≠ 0 := fun h0 => mul_ne_zero hf' (right_ne_zero_of_mul hy) (by rw [← map_mul, h0, map_zero])
  have h1 : ¬ ∀ q ∈ P, q.IsPrime → f' * g ∈ q := fun h1 => h0 (hP _ h1)
  push Not at h1
  obtain ⟨q, hq, -, hq'⟩ := h1
  obtain ⟨K', _, x', rfl, rfl⟩ := hρ q hq fun h2 => hq' (q.mul_mem_left _ h2)
  exact h' K' x' fun h2 => hq' (Ideal.mul_mem_right _ _ h2)

theorem exists_away_projective_vanIdeal : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (σ Hh : Type) [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ (∀ e ≥ d, Module.Projective (Localization.Away f) (↥(MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e) ⧸ ((vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).restrictScalars (Localization.Away f)).comap (MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e).subtype)) ∧ ∀ (K : Type) [Field K] (x : (Localization.Away f) →+* K), (vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).map (MvPolynomial.map x) = vanIdeal d (fun h i => x ((algebraMap R (Localization.Away f)) (p h i))) := by
  intro R _ _ _ σ Hh _ _ p Q d P hP hcut q₀ hq₀
  classical
  obtain ⟨K₀, _, x₀, I₀, rfl, hc₀⟩ := hcut q₀ hq₀
  have hI := component_mem_vanIdeal d p
  obtain ⟨f₁, hf₁, h₁⟩ := exists_const_near hP
    (fun K _ x => (dimDeg (vanIdeal d fun h i => x (p h i)) d : ℚ)) (Q.eval (d : ℚ)) 1
    (fun K _ x => (exists_dimDeg_vanIdeal_le d p K x).imp fun f hf =>
      ⟨hf.1, fun L _ y hy => Nat.cast_le.2 (hf.2 L y hy)⟩)
    (fun q hq _ => by
      obtain ⟨K, _, x, I, hx, hc⟩ := hcut q hq
      exact ⟨K, _, x, hx, dimDeg_eq_of_cutBy hc le_rfl⟩)
    K₀ x₀ (by simp) (dimDeg_eq_of_cutBy hc₀ le_rfl)
  have h₂ := map_vanIdeal_of_const_away d p _ f₁ h₁
  have h₃ : ∀ e ≥ d, ∃ g : R, x₀ g ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y g ≠ 0 →
      (dimDeg ((vanIdeal d p).map (MvPolynomial.map y)) e : ℚ) = Q.eval (e : ℚ) := by
    intro e he
    obtain ⟨g, hg, h⟩ := exists_const_near hP
      (fun K _ x => -(dimDeg ((vanIdeal d p).map (MvPolynomial.map x)) e : ℚ)) (-Q.eval (e : ℚ)) f₁
      (fun K _ x => (exists_dimDeg_map_le _ hI e K x).imp fun f hf =>
        ⟨hf.1, fun L _ y hy => neg_le_neg (Nat.cast_le.2 (hf.2 L y hy))⟩)
      (fun q hq hq' => by
        obtain ⟨K, _, x, I, rfl, hc⟩ := hcut q hq
        exact ⟨K, _, x, rfl, by rw [h₂ K x hq', dimDeg_eq_of_cutBy hc he]⟩)
      K₀ x₀ hf₁ (by rw [h₂ K₀ x₀ hf₁, dimDeg_eq_of_cutBy hc₀ he])
    exact ⟨g, hg, fun L _ y hy => neg_injective (h L y hy)⟩
  have h₄ : ∀ φ : ℕ → ℕ, ∃ g : R, x₀ g ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y g ≠ 0 →
      φ = dimDeg ((vanIdeal d p).map (MvPolynomial.map y)) → ∀ e ≥ d, (φ e : ℚ) = Q.eval (e : ℚ) := by
    intro φ
    by_cases hφ : ∀ e ≥ d, (φ e : ℚ) = Q.eval (e : ℚ)
    · exact ⟨1, by simp, fun _ _ _ _ _ => hφ⟩
    · push Not at hφ
      obtain ⟨e, he, hne⟩ := hφ
      obtain ⟨g, hg, h⟩ := h₃ e he
      exact ⟨g, hg, fun L _ y hy hφ => absurd (hφ ▸ h L y hy) hne⟩
  choose g hg h₅ using h₄
  have hfin := GlobalTheory.T.finite_setOf_hilbertFunctions_fibres R σ (vanIdeal d p) hI
  let f : R := f₁ * ∏ φ ∈ hfin.toFinset, g φ
  have h₆ : ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → ∀ e ≥ d,
      (dimDeg (vanIdeal d fun h i => y (p h i)) e : ℚ) = Q.eval (e : ℚ) := by
    intro L _ y hy
    simp only [f, map_mul, map_prod, ne_eq, mul_eq_zero, not_or] at hy
    rw [← h₂ L y hy.1]
    exact h₅ _ L y (Finset.prod_ne_zero_iff.1 hy.2 _ (hfin.mem_toFinset.2 ⟨L, _, y, rfl⟩)) rfl
  have hf : f ∉ RingHom.ker x₀ := by
    rw [RingHom.mem_ker, map_mul, map_prod]
    exact mul_ne_zero hf₁ (Finset.prod_ne_zero_iff.2 fun φ _ => hg φ)
  haveI : IsReduced (Localization.Away f) :=
    isReduced_localizationPreserves (Submonoid.powers f) _ inferInstance
  have h₇ : ∀ (L : Type) [Field L] (y : Localization.Away f →+* L), ∀ e ≥ d,
      (dimDeg (vanIdeal d fun h i => y (algebraMap R (Localization.Away f) (p h i))) e : ℚ) = Q.eval (e : ℚ) :=
    fun L _ y => h₆ L (y.comp (algebraMap R _))
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map y).ne_zero
  have h₈ := map_vanIdeal_of_const d (fun h i => algebraMap R (Localization.Away f) (p h i)) _
    fun L _ y => h₇ L y d le_rfl
  exact ⟨f, hf, fun e he => projective_of_const _ (component_mem_vanIdeal d _) e (Q.eval (e : ℚ))
    fun L _ y => by rw [h₈ L y]; exact h₇ L y e he, fun K _ x => h₈ K x⟩

end GlobalTheory.ZM.FormsFamily

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSquaredThetaTermsTorusCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralExpressionValuesAtDescendedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.Coef

theorem ev_units_zpow {V K : Type} [CommRing V] [Field K] (f : V →+* K) (v : Vˣ) (n : ℤ) :
    f ((v ^ n : Vˣ) : V) = f v ^ n := by
  have h1 : f ((v ^ n : Vˣ) : V) = ((Units.map f.toMonoidHom (v ^ n) : Kˣ) : K) := rfl
  rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem coef_sq_mem_monomial : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 = ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) ^ 2 = r * ∏ k, ev (s (.inr k)) ^ ε (.inr k) (e mu) (e mu) := by
  intro N₁ hN V₁ _ _ _ hV hunit D hpe htb X C _ e u mo hmo hT K _ _ ev k₀ hk₀ τ₀ m N s ε hs hτ hmo2 W₀ _ ib hB hib mu c
  obtain ⟨θ, b, t, χt, s₀, G, hθ, hb, ht, hχt, hs₀, hG, hGf⟩ :=
    GlobalTheory.T.integral_squaredThetaTerms_torusCoordinates N₁ hN V₁ hV hunit D hpe htb X C e u mo hmo hT τ₀ m N s ε hs hτ hmo2
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.integral_expression_values_at_descended_point N₁ hN V₁ hV hunit D X C e τ₀ θ hθ b hb t ht χt hχt G hGf K ev k₀ hk₀ W₀ ib hB hib
  obtain ⟨-, -, -, -, -, -, -, -, -, c₀, hc₀⟩ := hT
  have hc₀' : u 0 c₀ * mo 0 = 1 := hc₀
  have hm0 : mo 0 ^ 2 = 1 := by
    have h := hmo2 0
    simp only [map_zero, LinearMap.map_zero₂, zpow_zero, Finset.prod_const_one] at h
    exact IsFractionRing.injective V₁ (FractionRing V₁) (by simpa using h)
  have hu0 : u 0 c₀ ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hc₀'
    simpa only [mul_pow, hm0, _root_.mul_one, one_pow] using h
  have hP0 : ((∏ k, (hs k).unit ^ ε (.inr k) (e 0) (e 0) : V₁ˣ) : V₁) = 1 := by
    simp only [map_zero, LinearMap.map_zero₂, zpow_zero, Finset.prod_const_one, Units.val_one]
  have h0 : s₀ = G 0 c₀ := by
    have h := hG 0 c₀
    rw [hu0, _root_.one_mul, hP0, _root_.one_mul] at h
    exact h
  obtain ⟨r₀, hr₀, e₀⟩ := hΛ 0 c₀
  obtain ⟨r, hr, e₁⟩ := hΛ mu c
  have hev0 : ev s₀ ≠ 0 := (hs₀.map ev).ne_zero
  have hΛr₀ : Λ * r₀ ≠ 0 := by rw [← e₀, ← h0]; exact hev0
  have hr₀0 : r₀ ≠ 0 := right_ne_zero_of_mul hΛr₀
  have hΛ0 : Λ ≠ 0 := left_ne_zero_of_mul hΛr₀
  refine ⟨r / r₀, k₀.div_mem hr hr₀, ?_⟩
  have h := congrArg ev (hG mu c)
  rw [map_mul, map_mul, map_pow, e₁, h0, e₀, Units.coe_prod, map_prod] at h
  simp only [ev_units_zpow, IsUnit.unit_spec] at h
  field_simp
  apply mul_left_cancel₀ hΛ0
  linear_combination h

end GlobalTheory.USep.Coef

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedIsoPulledBackPeriodRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsDiagMemMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataFromLowerBaseAfterMonomialExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_periods_of_pull : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → (∀ a : Fin L.T.r → ℤ, ∃ x : Sp V₁ ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ x ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w) ∧ ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ lb pts
  choose x hx using pts
  let y : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B') := fun a => Over.homMk (x a) (hx a).1
  have hy : ∀ a, (y a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧
      (y a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left := fun a => ⟨(hx a).2.1, (hx a).2.2⟩
  obtain ⟨w₁, q, hg, hn, hP⟩ :=
    GlobalTheory.T.exists_normalised_iso_pulledBack_period_relation n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ lb y hy
  exact ⟨q, GlobalTheory.T.pulledBack_period_constants_symmetric n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP hn,
    GlobalTheory.T.pulledBack_period_constants_multiplicative n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP hn,
    GlobalTheory.T.pulled_back_period_constants_diag_mem_maximal n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP,
    GlobalTheory.T.degData_from_lowerBase_after_monomial_extension n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP⟩

end GlobalTheory.TChart

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinedDegenerationDataFiniteExtensionLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupLevelCoverEveryPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem exists_setup_regAt_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ev ∧ RegAt X₁ z₁ ev ∧ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧ Refines Q ρ D₀.toPre e₀ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsym hnn hpos hmono ξ hU l hl hln j₀
  obtain ⟨j, Y, q, hj, hqf, hqs, hB⟩ := GlobalTheory.T.exists_thetaSetup_levelCover_every_point g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth l hl hln j₀
  obtain ⟨V₁, _, _, _, ρ, D₀, e₀, y, y', hcn, hinj, hfin, href, hy, hy'⟩ :=
    GlobalTheory.T.exists_refined_degenerationData_finiteExtension_lift g n F Z i W hW V Q m t δ hrk ht hsym hnn hpos hmono ξ hU Y q hqf hqs
  obtain ⟨X₁, yM, hrN, hyM, hreg⟩ := hB (FractionRing V₁) y'
  obtain ⟨z₁, ev, hloc, he1, he2⟩ := GlobalTheory.T.exists_stalk_lift_finite_cover_normal_local V₁ hcn.2.1 X₁.M.Z Z X₁.π X₁.fin (spMap ρ ≫ ξ) yM
    (by rw [hyM, ← Category.assoc, hy', hy])
  refine ⟨j, X₁, z₁, V₁, inferInstance, inferInstance, inferInstance, ρ, ev, D₀, e₀, hj, hrN, hcn, hinj, hfin, hloc, ?_, he1,
    href⟩
  intro a ha
  rw [he2]
  exact hreg a ha

end GlobalTheory.Poinc.Sep

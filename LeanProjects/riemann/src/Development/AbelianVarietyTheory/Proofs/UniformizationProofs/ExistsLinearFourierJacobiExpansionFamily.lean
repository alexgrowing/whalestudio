import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverFieldStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjectiveStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLinMap

theorem exists_linear_of_rel {F M X : Type} [Field F] [AddCommGroup M] [Module F M] {N : X → Type}
    [∀ α, AddCommGroup (N α)] [∀ α, Module F (N α)] (E : M → (∀ α, N α) → Prop)
    (tot : ∀ t, ∃ s, E t s) (uq : ∀ t t' s s', E t s → E t' s' → (t = t' ↔ s = s'))
    (lin : ∀ (c : F) t t' s s', E t s → E t' s' → E (c • t + t') (fun α => c • s α + s' α)) :
    ∃ ex : ∀ α, M →ₗ[F] N α, (∀ t, E t (fun α => ex α t)) ∧ (∀ t s, E t s → ∀ α, s α = ex α t) ∧
      (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, ((∃ t s, E t s ∧ s α ≠ 0) ↔ ex α ≠ 0) := by
  choose e he using tot
  have hl : ∀ (c : F) t t' α, e (c • t + t') α = c • e t α + e t' α := fun c t t' α =>
    congrFun ((uq _ _ _ _ (he _) (lin c t t' _ _ (he t) (he t'))).1 rfl) α
  have h0 : ∀ α, e 0 α = 0 := fun α => by
    have h := hl 1 0 0 α
    simpa using h
  have hu : ∀ t s, E t s → ∀ α, s α = e t α := fun t s h α => congrFun ((uq _ _ _ _ h (he t)).1 rfl) α
  refine ⟨fun α => ⟨⟨fun t => e t α, fun t t' => ?_⟩, fun c t => ?_⟩, he, hu, fun t h => ?_, fun α => ⟨?_, fun h => ?_⟩⟩
  · simpa using hl 1 t t' α
  · simpa [h0] using hl c t 0 α
  · exact (uq _ _ _ _ (he t) (he 0)).2 (funext fun α => (h α).trans (h0 α).symm)
  · rintro ⟨t, s, h, hs⟩ hz
    exact hs ((hu t s h α).trans (LinearMap.congr_fun hz t))
  · by_contra hn
    refine h (LinearMap.ext fun t => ?_)
    by_contra ht
    exact hn ⟨t, e t, he t, ht⟩

theorem exists_expansion_linear : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U F _ _ k hk
  obtain ⟨ex, a, b, c, d⟩ := exists_linear_of_rel (F := F) (M := EA A (jFK (R := V) F) k) (N := fun α => WB D F k α)
    (fun t s => U.ExpF F k t.sec (fun α => (s α).sec))
    (fun t => GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D A G U F k hk t.sec)
    (fun t t' s s' h h' => GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k t.sec t'.sec _ _ h h')
    (fun c t t' s s' h h' => ExpLin.expF_linear V hV D A G U F k t.sec t'.sec _ _ _ _ c h h'
      (fun _ => rfl) (fun _ _ => rfl))
  refine ⟨ex, a, fun t s h α => b (SecMod.mk _ t) (fun α => SecMod.mk _ (s α)) h α, c, fun α => Iff.trans ?_ (d α)⟩
  constructor
  · rintro ⟨t, s, h, j, hj⟩
    exact ⟨SecMod.mk _ t, fun α => SecMod.mk _ (s α), h, fun hz => hj ((SecMod.eq_zero_iff_coord _).1 hz j)⟩
  · rintro ⟨t, s, h, hs⟩
    exact ⟨t.sec, fun α => (s α).sec, h, not_forall.1 fun hz => hs ((SecMod.eq_zero_iff_coord _).2 hz)⟩

end GlobalTheory.UU.ExpLinMap
end

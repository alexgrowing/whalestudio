import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreLinearHomsPrincipalCMTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilPairingEqCmIntegerOfPureTypeStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.FlatCM.GramExists

theorem exists_weilEq_entry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → p + q = 1 →
    HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ →
    Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ ρ σ₁ A B p q hρ hpq hA f₁ f₂ h₁ h₂
  obtain ⟨A', B', f₁', f₂', p', q', hpq', hdet, h₁', h₂', hW⟩ := GlobalTheory.T.exists_complex_fibre_linear_homs_principalCMTriple E H K ρ σ₁ A B p q hρ hA f₁ f₂ h₁ h₂
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_weil_pairing_eq_cm_integer_of_pure_type E H A' B' p' q' (hpq'.trans hpq) hdet f₁' f₂' h₁' h₂'
  exact ⟨g, hW g hg⟩

theorem exists_isGram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∃ gP gQ, IsGram X gP gQ := by
  intro E _ _ _ H K _ _ ρ σ₁ p q X
  have hP : ∀ a b : Fin p, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L
      ((X.A true).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP _ _ (X.lin (Sum.inl a)) (X.lin (Sum.inl b))
  have hQ : ∀ a b : Fin q, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L
      ((X.A false).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A false) X.B 0 1 X.ρ_sq rfl X.typeM _ _ (X.lin (Sum.inr a)) (X.lin (Sum.inr b))
  choose gP hgP using hP
  choose gQ hgQ using hQ
  exact ⟨Matrix.of gP, Matrix.of gQ, fun a b => hgP a b, fun a b => hgQ a b⟩

end GlobalTheory.FlatCM.GramExists

end

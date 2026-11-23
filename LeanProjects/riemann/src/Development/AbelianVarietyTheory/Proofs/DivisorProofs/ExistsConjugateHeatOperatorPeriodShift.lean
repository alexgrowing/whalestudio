import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeibnizAlongBaseConstantsAtPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjTranslationGaugeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFourierTermTranslationGaugeStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatDefect

theorem exists_gauge_translate : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])), e.IsGen → ∀ (k : ℕ) (τ : SecM Y.q.left Q.P.L k), ∃ ρ : SecM Y.q.left Q.P.L k, (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) := by
  intro R _ _ Q O _ _ _ oa Y x e he k τ
  obtain ⟨ρ, hρ⟩ := exists_sec (L := Q.P.L) Q.P.isLB
    (φ' := fun _ : Fin 1 => Y.q.left) (ε' := fun _ => (k : ℤ))
    (by
      intro U _ g
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [zpow_mul, zpow_mul, zpow_one, zpow_neg_one, _root_.mul_comm]
      exact inv_mul_cancel_right _ _)
    (pullMulSec τ (𝟙 Y.H * (toUnit Y.H ≫ x)).left (GeneratorPullback.powGen Q.P.L _ _ e k) (ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen _ _ _ e he k))
  refine ⟨ρ, fun Z r z J hJ => ?_⟩
  rw [hρ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ]
  congr 1
  exact congrArg Units.val (map_pow _ _ _)

theorem exists_conj_shift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∀ mu : Dd.toPre.X, ∃ (h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X →+ R) (π π' : R), IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) (σ₁ σ₁' : Dd.toPre.SecB k (α + k • mu)), 1 ≤ k → ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → TActs Y h k (α + k • mu) σ₁ σ₁' → ∃ σ'' : Dd.toPre.SecB k α, TActs Y h' k α σ σ'' ∧ ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hm ht D hD h hb mu
  obtain ⟨x, e, β, w, π, π', he, hwe, hTR⟩ := GlobalTheory.T.thetaShift_fourierTerm_translation_gauge R Dd O oa Y m t gam hm ht D hD mu
  obtain ⟨h', hb', hΘ, hu, hint⟩ :=
    GlobalTheory.T.heatOperator_conj_translation_gauge R Dd.toPre O oa Y n (fun a => v a) dd hv D h hb x e β he hwe
  refine ⟨h', w, π, π', hb', hΘ, hu, ?_⟩
  intro k α σ σ₁ σ₁' hk hs hA
  obtain ⟨τ₁, τ₁', hτ₁, hτ₁', hA₁⟩ := hA
  obtain ⟨σ'', τ, τ'', hτ, hτ'', hA'⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h' hb' k α σ
  obtain ⟨ρ, hρ⟩ := exists_gauge_translate Y x e he k τ₁
  obtain ⟨ρ', hρ'⟩ := exists_gauge_translate Y x e he k τ₁'
  have hAρ := hint k τ₁ τ₁' ρ ρ' hρ hρ' hA₁
  obtain ⟨a, b, -, hab⟩ := hTR k α hk
  obtain ⟨h1, h2⟩ := hab σ σ₁ τ τ₁ ρ hs hτ hτ₁ hρ
  exact ⟨σ'', ⟨τ, τ'', hτ, hτ'', hA'⟩, h2 σ'' σ₁' τ'' τ₁' ρ' hτ'' hτ₁' hρ'
    (GlobalTheory.T.leibniz_along_baseConstants_at_points Y.H Y.q.left Dd.toPre.P.L Dd.toPre.P.isLB (fun a => v a) dd hv D h' k a b ρ τ ρ' τ'' h1 hAρ hA')⟩

end GlobalTheory.HeatDefect

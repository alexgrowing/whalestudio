import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodReductionModelCmPeriodFibre
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodReduction_model_cmPeriod_fibre : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ) (_ : CMLat hP p q) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : Bool → 𝓞 K₁) (C : ∀ b, Ell H (𝓞 K₁) (ω b)) (ε : Bool → ℤˣ) (h : Bool → (FU.Di i).La → (FU.Di i).La → OK H) (B : PAT H (Sp (𝓞 K₁))) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁)) (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (ψ : ∀ b : Bool, PureType.lat hP (if b then H.rt0 else -H.rt0) → ((C b).P.A ⟶ B.t.G)) (ω' : Bool → ℂ) (C' : ∀ b, Ell H ℂ (ω' b)) (π : ∀ b, (C' b).P.A.left ⟶ (C b).P.A.left) (u₀ : ∀ b, HolUnif (C' b).P.A (C' b).P.L (C' b).P.g) (c : Bool → ℂ),
    k ≤ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
    ∀ b : Bool, 2 * ω' b - 1 = (if b then H.rt0 else -H.rt0) ∧ 0 < ((ε b : ℤ) : ℝ) * (ω' b).im ∧ IsKForm (FU.Di i) (ε b) (h b) ∧ IsFam (C b) B (h b) _ (ψ b) ∧ EllMap (C' b) (C b) ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) (π b) ∧ c b ≠ 0 ∧ PureType.IsQuadLattice (u₀ b).Λ H.d (c b) ∧
      ∀ a (z : ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) → x ≫ m'.φ = ((u₀ b).ex (fun _ => c b * z)).left ≫ π b ≫ (ψ b a).left → x ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  first | exact @GlobalTheory.CM.PeriodModel.exists_model | exact GlobalTheory.CM.PeriodModel.exists_model | (intros; apply GlobalTheory.CM.PeriodModel.exists_model <;> assumption)

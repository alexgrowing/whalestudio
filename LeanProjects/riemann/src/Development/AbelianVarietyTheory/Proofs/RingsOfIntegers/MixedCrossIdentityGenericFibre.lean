import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfPullAl
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalScale
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecEqOfThick

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericCross

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gs_scal {V : Type} [CommRing V] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of V)) (z : Z)
    (c : V) : gs r z ⊤ (scal p c) = cst (r ≫ p) z c := by
  unfold scal cst
  exact gs_pull r p z ⊤ (by simp) _

theorem isUnit_cst {V : Type} [CommRing V] [IsDomain V] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) {c : V} (hc : c ≠ 0) :
    IsUnit (cst (q ≫ jK V) z c) := by
  have hne : algebraMap V (FractionRing V) c ≠ 0 := fun h =>
    hc (IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero]))
  obtain ⟨u, hu⟩ := (IsUnit.mk0 _ hne).map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom
  have nat : ((jK V).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) c) :=
    (congrArg (fun g => g.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))).symm
  have h1 : cst (q ≫ jK V) z c = gs q z ⊤ (((jK V).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c)) :=
    (gs_pull q (jK V) z ⊤ (by simp) _).symm
  rw [h1, nat, ← hu, gs_unit q z ⊤ (by simp) u]
  exact Units.isUnit _

theorem endK_fst {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {G : Over (Spec (CommRingCat.of V))} (f : G ⟶ G) :
    endK f ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ f.left := by
  unfold endK
  exact pullback.lift_fst _ _ _

theorem endK_snd {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {G : Over (Spec (CommRingCat.of V))} (f : G ⟶ G) :
    endK f ≫ pullback.snd G.hom (jK V) = pullback.snd G.hom (jK V) := by
  unfold endK
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem main : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k₁ : ℕ) (s₁ : P.U.SecK k₁) (F₁ : Fam P.D.toPre (FractionRing V) k₁) (u₁ : P.U.SecK (k₁ * N)) (F₁' : Fam P.D.toPre (FractionRing V) (k₁ * N)), P.U.Expands k₁ s₁ F₁ → P.U.Expands (k₁ * N) u₁ F₁' → PullAl P.D (FractionRing V) P.oD a k₁ N F₁ F₁' → ∀ (k₂ : ℕ) (s₂ : P.U.SecK k₂) (F₂ : Fam P.D.toPre (FractionRing V) k₂) (u₂ : P.U.SecK (k₂ * N)) (F₂' : Fam P.D.toPre (FractionRing V) (k₂ * N)), P.U.Expands k₂ s₂ F₂ → P.U.Expands (k₂ * N) u₂ F₂' → PullAl P.D (FractionRing V) P.oD a k₂ N F₂ F₂' → ∀ m₁ m₂ : ℕ, m₁ * k₁ = m₂ * k₂ → ∀ (y : (pullback t.G.hom (jK V) : Scheme.{0})) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u₁ (𝟙 _) y J ^ m₁ * Geo.Tor.sval s₂ (endK (t.act.act a)) y J ^ m₂ = Geo.Tor.sval u₂ (𝟙 _) y J ^ m₂ * Geo.Tor.sval s₁ (endK (t.act.act a)) y J ^ m₁ := by
  intro hL V _ _ _ E _ _ _ H t P a N hN hN0 k₁ s₁ F₁ u₁ F₁' he₁ he₁' hp₁ k₂ s₂ F₂ u₂ F₂' he₂ he₂' hp₂
    m₁ m₂ hm y J hJ
  let _ : StarRing (NumberField.RingOfIntegers E) := H.starRing
  obtain ⟨uΨ, huΨ, -⟩ := P.w0
  obtain ⟨X, hX, hXc⟩ := exists_XB (D := P.D) (hL := P.D.toPre.P.isLB) (oa := P.oD) (w0 := H.w0) (uΨ := uΨ)
    (huΨ := huΨ) (a := a) (N := N) (hN := hN) (hN1 := by omega) (k := 1)
  obtain ⟨c₁, σ₁, τ₁, hc₁, hτ₁, hσ₁, ht₁⟩ := GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc
    k₁ s₁ F₁ u₁ F₁' he₁ he₁' hp₁
  obtain ⟨c₂, σ₂, τ₂, hc₂, hτ₂, hσ₂, ht₂⟩ := GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc
    k₂ s₂ F₂ u₂ F₂' he₂ he₂' hp₂
  have hx := GlobalTheory.MixedCross.main hL.lemmaB V E H t P a N hN hN0 X k₁ k₂ m₁ m₂ hm σ₁ τ₁ σ₂ τ₂ ht₁ ht₂ _
    (pullback.fst t.G.hom (jK V)) y J hJ
  have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hσ₁ (𝟙 _) y hJ
  have e₂ := GlobalTheory.PullIntegral.sval_of_secScal hσ₂ (𝟙 _) y hJ
  have f₁ := GlobalTheory.PullIntegral.sval_of_secScal hτ₁ (endK (t.act.act a)) y hJ
  have f₂ := GlobalTheory.PullIntegral.sval_of_secScal hτ₂ (endK (t.act.act a)) y hJ
  rw [gs_scal, Category.id_comp, Category.id_comp] at e₁ e₂
  rw [gs_scal, endK_fst, ← Category.assoc, endK_snd] at f₁ f₂
  rw [e₁, e₂, f₁, f₂] at hx
  have hu : IsUnit (cst (pullback.snd t.G.hom (jK V) ≫ jK V) y c₁ ^ m₁ *
      cst (pullback.snd t.G.hom (jK V) ≫ jK V) y c₂ ^ m₂) :=
    ((isUnit_cst _ y hc₁).pow m₁).mul ((isUnit_cst _ y hc₂).pow m₂)
  apply hu.mul_left_cancel
  linear_combination hx

end GlobalTheory.GenericCross

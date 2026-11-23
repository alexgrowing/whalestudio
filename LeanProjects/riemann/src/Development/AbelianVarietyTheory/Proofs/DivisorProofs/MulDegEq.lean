import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroResidueFieldGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2Indep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExceptional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFlagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlagCh2

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.VMetric

theorem FlagModel.mul_deg_eq (hA : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}}
    {p : X ⟶ Sp k} [IsIntegral X]
    (hreg : ∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q))
    (hX : IsArithVar p 1) {E : X.Modules} {r : ℕ} {h : VMetric p E r} (M₁ M₂ : h.FlagModel)
    {a₁ a₂ : ℝ} (h₁ : IsFlagCh2 M₁.cInf M₁.flag a₁) (h₂ : IsFlagCh2 M₂.cInf M₂.flag a₂) :
    a₁ * M₂.deg = a₂ * M₁.deg := by
  obtain ⟨Z, _, t₁, t₂, w, hZ, g₁, g₂, r₁, r₂⟩ :=
    RegCover.exists_common hX M₁.toRegCover M₂.toRegCover
  have e₁ : t₁ ≫ M₁.ρ ≫ p = (t₁ ≫ M₁.ρ) ≫ p := (Category.assoc _ _ _).symm
  have e₂ : t₂ ≫ M₂.ρ ≫ p = (t₁ ≫ M₁.ρ) ≫ p := by rw [w, Category.assoc]
  obtain ⟨f₁, F₁⟩ := GlobalTheory.FlagPull.isFlagCh2_pull hA k _ _ Z _ M₁.reg.toIsArithVar hZ t₁ e₁ g₁ r₁
    _ _ _ M₁.cInf M₁.flag
  obtain ⟨f₂, F₂⟩ := GlobalTheory.FlagPull.isFlagCh2_pull hA k _ _ Z _ M₂.reg.toIsArithVar hZ t₂ e₂ g₂ r₂
    _ _ _ M₂.cInf M₂.flag
  have key : ∀ (Y : Scheme.{0}) (ρ : Y ⟶ X) (t : Z ⟶ Y) (u : Z ⟶ X) (q : Z ⟶ Sp k) (_ : t ≫ ρ = u)
      (hu : u ≫ p = q) (e : t ≫ ρ ≫ p = q) (H : ((h.pull ρ rfl).pull t e).IsCInf)
      (f : Vert.Flag ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ρ).obj E)) r) (a : ℝ),
      IsFlagCh2 H f a → ∃ (H' : (h.pull u hu).IsCInf)
        (f' : Vert.Flag ((Scheme.Modules.pullback u).obj E) r), IsFlagCh2 H' f' a := by
    rintro Y ρ t _ q rfl hu e H f a ha
    have I := (GlobalTheory.VMetric.isIsometry_pull_id_comp k X p E r h).2 Y Z _ q ρ t rfl e hu
    have H' : (h.pull (t ≫ ρ) hu).IsCInf := by
      rw [(VMetric.isIsometry_iff _).1 I]
      exact H.map _
    exact ⟨H', _, (GlobalTheory.VMetric.isFlagCh2_ofIso k Z q _ _ r _ _ _ H H' f a I).1 ha⟩
  obtain ⟨H₁, f₁', A₁⟩ := key _ M₁.ρ t₁ _ _ rfl rfl e₁ _ f₁ _ ((F₁ a₁).1 h₁)
  obtain ⟨H₂, f₂', A₂⟩ := key _ M₂.ρ t₂ _ _ w.symm rfl e₂ _ f₂ _ ((F₂ a₂).1 h₂)
  have A := GlobalTheory.isFlagCh2_indep hA k Z _ hreg hZ _ r _ H₁ f₁' f₂' _ _ A₁ A₂
  have d : M₁.deg * t₁.residueDegree (genericPoint Z) =
      M₂.deg * t₂.residueDegree (genericPoint Z) := by
    have c₁ := CurveDegreesCompare.residueDegree_comp t₁ M₁.ρ (genericPoint Z)
    have c₂ := CurveDegreesCompare.residueDegree_comp t₂ M₂.ρ (genericPoint Z)
    rw [g₁] at c₁
    rw [g₂, ← w, c₁] at c₂
    exact c₂
  have d' : (M₁.deg : ℝ) * t₁.residueDegree (genericPoint Z) =
      M₂.deg * t₂.residueDegree (genericPoint Z) := by exact_mod_cast d
  have n₂ : (t₂.residueDegree (genericPoint Z) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 r₂
  refine mul_left_cancel₀ n₂ ?_
  linear_combination (M₁.deg : ℝ) * A - a₁ * d'

theorem IsCInfNorm.exists_isCh2Deg (hA : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}}
    {p : X ⟶ Sp k} [IsIntegral X]
    (hreg : ∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q))
    (hX : IsArithVar p 1) {E : X.Modules} {r : ℕ} {h : VMetric p E r} (hn : h.IsCInfNorm) :
    ∃ a, h.IsCh2Deg a := by
  obtain ⟨M₀⟩ := GlobalTheory.FlagModelExists.nonempty_flagModel k X p hreg hX E r h hn
  obtain ⟨a₀, h₀⟩ := GlobalTheory.VMetric.exists_isFlagCh2 hA k _ _ M₀.reg _ r _ M₀.cInf M₀.flag
  refine ⟨a₀ / M₀.deg, ⟨M₀⟩, fun M => ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.VMetric.exists_isFlagCh2 hA k _ _ M.reg _ r _ M.cInf M.flag
  have e := FlagModel.mul_deg_eq hA hreg hX M₀ M h₀ ha
  have n : (M₀.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M₀.deg_pos.ne'
  convert ha using 1
  field_simp
  linear_combination e

end GlobalTheory.VMetric

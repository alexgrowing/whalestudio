import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroResidueFieldGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2Indep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFlagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExceptional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlagCh2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

theorem GlobalTheory.VMetric.exists_isCh2Deg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], (∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q)) → IsArithVar p 1 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r), h.IsCInfNorm → ∃ a, h.IsCh2Deg a := by
  intro hA k _ X p _ hR hX E r h H
  obtain ⟨M⟩ := GlobalTheory.FlagModelExists.nonempty_flagModel k X p hR hX E r h H
  have hex (N : h.FlagModel) : ∃ c, VMetric.IsFlagCh2 N.cInf N.flag c :=
    GlobalTheory.VMetric.exists_isFlagCh2 hA k N.Y (N.ρ ≫ p) N.reg _ r _ N.cInf N.flag
  obtain ⟨c, hc⟩ := hex M
  refine ⟨c / M.deg, ⟨M⟩, fun N => ?_⟩
  obtain ⟨d, hd⟩ := hex N
  obtain ⟨Z, _, t₁, t₂, e, hZ, g₁, g₂, r₁, r₂⟩ :=
    RegCover.exists_common hX M.toRegCover N.toRegCover
  have e₁ : t₁ ≫ M.ρ ≫ p = (t₁ ≫ M.ρ) ≫ p := (Category.assoc _ _ _).symm
  have e₂ : t₂ ≫ N.ρ ≫ p = (t₁ ≫ M.ρ) ≫ p := by rw [e, Category.assoc]
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.FlagPull.isFlagCh2_pull hA k M.Y (M.ρ ≫ p) Z _ M.reg.toIsArithVar hZ t₁ e₁
    g₁ r₁ _ r _ M.cInf M.flag
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.FlagPull.isFlagCh2_pull hA k N.Y (N.ρ ≫ p) Z _ N.reg.toIsArithVar hZ t₂ e₂
    g₂ r₂ _ r _ N.cInf N.flag
  have i₁ := (GlobalTheory.VMetric.isIsometry_pull_id_comp k X p E r h).2 M.Y Z _ _ M.ρ t₁ rfl e₁ rfl
  have i₂ := (GlobalTheory.VMetric.isIsometry_pull_id_comp k X p E r h).2 N.Y Z _ _ N.ρ t₂ rfl e₂
    ((Category.assoc _ _ _).trans e₂)
  have key : ∀ (u : Z ⟶ X) (hu : u ≫ p = (t₁ ≫ M.ρ) ≫ p) (_ : t₁ ≫ M.ρ = u)
      (G : (h.pull u hu).IsCInf) (fl : Vert.Flag _ r) (y : ℝ), VMetric.IsFlagCh2 G fl y →
      (t₁.residueDegree (genericPoint Z) : ℝ) * c = y := by
    rintro u hu rfl G fl y hy
    exact GlobalTheory.isFlagCh2_indep hA k Z _ hR hZ _ r _ G _ fl _ _
      ((GlobalTheory.VMetric.isFlagCh2_ofIso k Z _ _ _ r _ _ _ _ G f₁ _ i₁).1 ((hf₁ c).1 hc)) hy
  have G₂ : (h.pull (t₂ ≫ N.ρ) ((Category.assoc _ _ _).trans e₂)).IsCInf := by
    rw [(VMetric.isIsometry_iff _).1 i₂]
    exact (N.cInf.pull t₂ e₂).map _
  have k₁ := key _ _ e G₂ _ _
    ((GlobalTheory.VMetric.isFlagCh2_ofIso k Z _ _ _ r _ _ _ _ G₂ f₂ _ i₂).1 ((hf₂ d).1 hd))
  have k₂ : M.deg * t₁.residueDegree (genericPoint Z) = N.deg * t₂.residueDegree (genericPoint Z) := by
    have := congrArg (fun u : Z ⟶ X => u.residueDegree (genericPoint Z)) e
    simp only [CurveDegreesCompare.residueDegree_comp] at this
    rw [g₁, g₂] at this
    exact this
  have k₃ : (M.deg : ℝ) * t₁.residueDegree (genericPoint Z) =
      N.deg * t₂.residueDegree (genericPoint Z) := by exact_mod_cast k₂
  have n₁ : (M.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.deg_pos.ne'
  have n₂ : (t₂.residueDegree (genericPoint Z) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 r₂
  have : (N.deg : ℝ) * (c / M.deg) = d := by
    apply mul_left_cancel₀ n₂
    rw [← k₁, ← mul_assoc, mul_comm _ (N.deg : ℝ), ← k₃]
    field_simp
  rwa [this]

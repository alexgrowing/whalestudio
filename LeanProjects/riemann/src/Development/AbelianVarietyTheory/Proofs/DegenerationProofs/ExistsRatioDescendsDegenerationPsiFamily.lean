import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_psi_ratio {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (ψ : TauTwist.PsiFam D)
    (hψ : ∀ χ, (ψ χ).IsGen) (χ : D.X) : ∃ u : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
      val (D.psi χ) (𝟙 _) z J = TauTwist.unitAt (A := FractionRing R) (Z := (TK R).left) (𝟙 _) z u * val (ψ χ) (𝟙 _) z J :=
  TauTwist.exists_ratio (F := FractionRing R) D.P.isLB (fun _ _ _ => rfl) (D.psi_gen χ) (hψ χ)

theorem unitAt_genMap {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (z : (TK K).left) (v : (FractionRing K₁)ˣ) :
    TauTwist.unitAt (A := FractionRing K₁) (genMap β.injective) z v =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom v) :=
  (congrArg (fun r => TauTwist.unitAt (A := FractionRing K₁) r z v) (Category.id_comp _).symm).trans
    (TauTwist.unitAt_spMap (𝟙 _) (fracMap β.injective) z v)

theorem exists_isPullDeg_rescale {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (D₁ : DegPre K₁) (D : DegPre K)
    (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ))
    (q : D₁.X → (FractionRing K₁)ˣ)
    (hq : ∀ χ (z : (TK K).left) J, Good D.P.L z J → val (D.psi χ) (𝟙 _) z J =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ))) *
        val (ψ χ) (𝟙 _) z J) :
    ∃ hD : IsPullDeg β (TauTwist.rescale D₁ q) D, proj hD = proj h := by
  have key : ∀ (x : D.X) (z : (TK K).left) J J', Good D₁.P.L z J → Good D.P.L z J' →
      val ((TauTwist.rescale D₁ q).psi (h.xe x)) (genMap β.injective) z J =
        (om h.w z J J' (D.xK x))⁻¹ * val (D.psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    have e := psi_val (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h (genMap β.injective) (𝟙 _) (fracMap_sq β.injective) hJ hJ' x
    rw [Category.id_comp] at e
    refine (TauTwist.val_psi_rescale q (h.xe x) _ hJ).trans ((congrArg₂ (· * ·) (unitAt_genMap β z _) e).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg₂ (· * ·) rfl (hq x z J' hJ')).symm
  obtain ⟨hD, hp, -, -⟩ := exists_isPullDeg_of_val β (TauTwist.rescale D₁ q) D (Φ := proj (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h)
    (pull_grp (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.w
    ((isGen_iff h.w).1 h.w_gen) (pmaps_rig (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.xe h.c_pr key
  exact ⟨hD, hp⟩

theorem exists_ratio_descends (K : Type) [Field K] (D : DegPre K) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) :
    ∃ a : D.X → K, ∀ (K₁ : Type) [Field K₁] (β : K₁ →+* K) (D₁ : DegPre K₁)
      (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ)), (∀ χ, a χ ∈ Set.range β) →
      ∃ (ψ₁ : TauTwist.PsiFam D₁) (hψ₁ : ∀ χ, (ψ₁ χ).IsGen) (hD : IsPullDeg β (TauTwist.withPsi D₁ ψ₁ hψ₁) D),
        PsiEvenPull.proj hD = PsiEvenPull.proj h := by
  choose u hu using exists_psi_ratio D ψ hψ
  refine ⟨fun χ => FractionRing.algEquiv K K (u χ).val, fun K₁ _ β D₁ h ha => ?_⟩
  choose a₁ ha₁ using ha
  have key : ∀ χ, fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ χ)) = (u χ).val := fun χ => by
    rw [fracMap_algebraMap, ha₁]
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  have hne : ∀ χ, algebraMap K₁ (FractionRing K₁) (a₁ χ) ≠ 0 := fun χ e => (u χ).ne_zero (by
    rw [← key, e, map_zero])
  obtain ⟨q, hq⟩ : ∃ q : D₁.X → (FractionRing K₁)ˣ,
      ∀ χ, Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ)) = u χ :=
    ⟨fun y => Units.mk0 _ (hne (h.xe.symm y)), fun χ => Units.ext (by
      show fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ (h.xe.symm (h.xe χ)))) = _
      rw [AddEquiv.symm_apply_apply, key])⟩
  obtain ⟨hD, hp⟩ := exists_isPullDeg_rescale β D₁ D ψ hψ h q fun χ z J hJ => by
    rw [hq]; exact hu χ z J hJ
  exact ⟨_, _, hD, hp⟩

end GlobalTheory.FieldPull
end

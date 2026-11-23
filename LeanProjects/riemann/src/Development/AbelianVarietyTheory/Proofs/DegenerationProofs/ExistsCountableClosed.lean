import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdditivePointsDescendFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenTauBimultDescendOfInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOrderActionDescentFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelationDescendsFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFieldsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamilyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_countable_closed {K : Type} [Field K] [IsAlgClosed K] (K₀ : Subfield K) [Countable K₀] {X : Type}
    [Countable X] (a : X → K) : ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (α : K₀ →+* F₁)
      (β : F₁ →+* K), β.comp α = K₀.subtype ∧ ∀ x, a x ∈ Set.range β := by
  let K₁ : Subfield K := Subfield.closure ((K₀ : Set K) ∪ Set.range a)
  have hc : ((K₀ : Set K) ∪ Set.range a).Countable := (Set.to_countable _).union (Set.countable_range a)
  have c₁ : Cardinal.mk K₁ ≤ Cardinal.aleph0 :=
    (Subfield.cardinalMk_closure_le_max _).trans (max_le (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype) le_rfl)
  have h : K₀ ≤ K₁ := fun x hx => Subfield.subset_closure (Or.inl hx)
  let β : AlgebraicClosure K₁ →ₐ[K₁] K := IsAlgClosed.lift
  refine ⟨AlgebraicClosure K₁, inferInstance, inferInstance, ?_, (algebraMap K₁ _).comp (Subfield.inclusion h),
    β.toRingHom, RingHom.ext fun x => β.commutes _, fun x =>
      ⟨algebraMap K₁ _ ⟨a x, Subfield.subset_closure (Or.inr ⟨x, rfl⟩)⟩, β.commutes _⟩⟩
  exact Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max K₁ _).trans (max_le c₁ le_rfl))

theorem exists_pre (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] {O : Type} [CommRing O] [StarRing O]
    [Module.Finite ℤ O] (D : DegPre K) (o : D.P.OAct O) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (β : F₁ →+* K) (D₁ : DegPre F₁)
      (hD : IsPullDeg β D₁ D) (o₁ : D₁.P.OAct O), ∀ a, (o.act a).left ≫ proj hD = proj hD ≫ (o₁.act a).left := by
  obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := D.X)
  have hgen' : Subring.closure (Set.range gen) = ⊤ := top_le_iff.1 fun x _ => by
    have hx : x ∈ Submodule.span ℤ (Set.range gen) := hgen ▸ Submodule.mem_top
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hx
    exact (AddSubgroup.closure_le (Subring.closure (Set.range gen)).toAddSubgroup).2 Subring.subset_closure hx
  have hb' : AddSubgroup.closure (Set.range b) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hb]; rfl
  obtain ⟨K₀, P₀, Φ, a₀, x₀, hc, gp, hw, ha, hx⟩ :=
    GlobalTheory.T.polAV_descends_to_countable_subfield' K D.P (Fin n) (Fin m) (fun j => o.act (gen j)) (fun k => D.c (b k))
  obtain ⟨o₀, ho₀⟩ := GlobalTheory.T.polarisedRingAction_descend_of_generators O _ gen hgen' K₀ K _ P₀ D.P Φ gp hw o a₀ ha
  obtain ⟨c₀, hc₀, hc₁⟩ := GlobalTheory.T.additive_points_descend_field_extension K₀ K _ P₀ D.P Φ gp D.X _ b hb' D.c D.c_add x₀ hx
  obtain ⟨D₀, ψ, hψ, h₀, rfl, e⟩ := GlobalTheory.T.exists_degenerationPreData_over_subfield hL K₀ K _ D P₀ Φ gp hw c₀ hc₀ hc₁
  obtain rfl := eq_of_heq e
  obtain ⟨a, Ha⟩ := GlobalTheory.T.exists_ratio_descends_degenerationPsiFamily K D ψ hψ
  have : Countable D.X := Finsupp.Countable.of_moduleFinite (R := ℤ)
  obtain ⟨F₁, _, _, _, α, β, hαβ, hβ⟩ := exists_countable_closed K₀ a
  obtain ⟨D', h₁, -, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange K₀ F₁ α D₀ ⊤ (nonempty_psiOn_field D₀) trivial
  generalize K₀.subtype = i at h₀ ho₀ hαβ
  subst hαβ
  obtain ⟨h₂, e₂⟩ := GlobalTheory.T.exists_pullDeg_cancel_tower_of_fields K₀ F₁ K α β D₀ D' _ h₁ h₀
  obtain ⟨ψ₁, hψ₁, hD, e₃⟩ := Ha F₁ β D' h₂ hβ
  obtain ⟨o₁, ho₁⟩ := polOActPull _ _ _ D₀.P D'.P _ (pull_grp h₁) (LBIso.symm ⟨h₁.w, h₁.w_gen⟩) O o₀
  refine ⟨F₁, inferInstance, inferInstance, inferInstance, β, _, hD, o₁, fun c => ?_⟩
  rw [e₃]
  refine (pull_grp h₁).1.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans ((ho₀ c).trans ((congrArg (· ≫ _) e₂.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ho₁ c).symm).trans (Category.assoc _ _ _).symm)))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pull_grp h₂).1.w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w (o.act c))).trans ((pull_grp h₂).1.w.symm.trans
        ((congrArg (_ ≫ ·) (Over.w (o₁.act c)).symm).trans (Category.assoc _ _ _).symm)))))

theorem exists_data (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] {O : Type} [CommRing O] [StarRing O]
    [Module.Finite ℤ O] (D : DegPre K) [Module O D.X] (oa : D.OAct O) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (β : F₁ →+* K) (D₁ : DegPre F₁)
      (hD : IsPullDeg β D₁ D) (_ : Module O D₁.X) (oa₁ : D₁.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) ∧
      (∀ a, (oa.onB.act a).left ≫ proj hD = proj hD ≫ (oa₁.onB.act a).left) ∧ (D.PsiEven → D₁.PsiEven) ∧
      (D.TauBimult → D₁.TauBimult) ∧ ∀ w, TraceFormTwistIso D oa w → TraceFormTwistIso D₁ oa₁ w := by
  obtain ⟨F₁, _, _, _, β, D₁, hD, o₁, ho⟩ := exists_pre hL D oa.onB
  letI : Module O D₁.X := hD.xe.symm.module O
  have hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y := fun a y => by
    show _ = hD.xe (a • hD.xe.symm (hD.xe y))
    rw [AddEquiv.symm_apply_apply]
  obtain ⟨oa₁, rfl⟩ := GlobalTheory.T.exists_orderAction_descent_field_extension hL.globalFns F₁ K β D₁ D hD O o₁ oa hx ho
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.psiEven_tauBimult_descend_of_injective hL.globalFns F₁ K β β.injective D₁ D hD
  exact ⟨F₁, inferInstance, inferInstance, inferInstance, β, D₁, hD, inferInstance, oa₁, hx, ho, h₁, h₂,
    GlobalTheory.T.psi_relation_descends_field_extension hL.globalFns F₁ K β D₁ D hD O oa₁ oa hx ho⟩

end GlobalTheory.FieldPull
end

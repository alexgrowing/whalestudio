import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericExtend

theorem eq_of_valR_eq {Y : Scheme.{0}} [IsReduced Y] {V : Y.Opens} {f g : Γ(Y, V)}
    (H : ∀ x ∈ V, ∃ (K : Type) (_ : Field K) (h : Sp K ⟶ Y), (∀ o, h o = x) ∧
      valR h V f = valR h V g) : f = g := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  exfalso
  have hxV := Y.basicOpen_le _ hx
  obtain ⟨K, _, h, ho, hv⟩ := H x hxV
  have h₁ : ⊤ ≤ h ⁻¹ᵁ V := fun o _ ↦ show h o ∈ V from (ho o).symm ▸ hxV
  have h₂ := (Points.le_preimage_basicOpen_iff h h₁ (f - g)).1
    fun o _ ↦ show h o ∈ Y.basicOpen (f - g) from (ho o).symm ▸ hx
  rw [Points.valR_eq h V h₁, Points.valR_eq h V h₁] at hv
  rw [Points.valR_eq h V h₁, map_sub, hv, sub_self] at h₂
  exact not_isUnit_zero h₂

theorem compat_of_valF {Q Y : Scheme.{0}} [IsReduced Q] {N : LB Y} {J : Q ⟶ Y}
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ}
    (H : ∀ (a b : N.ι) (K : Type) [Field K] (h : Sp K ⟶ Q), Set.range (h ≫ J) ⊆ N.U a →
      Set.range (h ≫ J) ⊆ N.U b →
      valF h _ (τ a).val = valF (h ≫ J) _ (N.g a b).val * valF h _ (τ b).val) :
    Compat N J τ := by
  intro Z r z a b ha hb
  have l₁ : J ⁻¹ᵁ (N.U a ⊓ N.U b) ≤ J ⁻¹ᵁ N.U a := J.preimage_mono inf_le_left
  have l₂ : J ⁻¹ᵁ (N.U a ⊓ N.U b) ≤ J ⁻¹ᵁ N.U b := J.preimage_mono inf_le_right
  have key : res l₁ (τ a) = pullU J _ (N.g a b) * res l₂ (τ b) := by
    refine Units.ext (eq_of_valR_eq fun x hx ↦ ⟨Q.residueField x, inferInstance,
      Q.fromSpecResidueField x, fun o ↦ Scheme.fromSpecResidueField_apply x o, ?_⟩)
    have ho : ∀ o, (Q.fromSpecResidueField x : Sp (Q.residueField x) ⟶ Q) o = x :=
      fun o ↦ Scheme.fromSpecResidueField_apply x o
    generalize (Q.fromSpecResidueField x : Sp (Q.residueField x) ⟶ Q) = h at ho
    have h₁ : ⊤ ≤ h ⁻¹ᵁ J ⁻¹ᵁ (N.U a ⊓ N.U b) := fun o _ ↦
      show h o ∈ J ⁻¹ᵁ (N.U a ⊓ N.U b) from (ho o).symm ▸ hx
    have := H a b _ h (by rintro _ ⟨o, rfl⟩; exact (h₁ (x := o) trivial).1)
      (by rintro _ ⟨o, rfl⟩; exact (h₁ (x := o) trivial).2)
    rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_comp,
      ← Points.valR_res h l₁ h₁, ← Points.valR_res h l₂ h₁, ← Points.valR_mul _ _ h₁] at this
    exact this
  have hz : r z ∈ J ⁻¹ᵁ (N.U a ⊓ N.U b) := ⟨ha, hb⟩
  have := congrArg (gm r z _) key
  rwa [map_mul, gm_res r z l₁ hz, gm_res r z l₂ hz, gm_pull r J z _ hz] at this

theorem exists_unit_extend_of_generic : ∀ (X P : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] (j : Sp Ω ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → ∀ (p : P ⟶ X) (e : X ⟶ P) (N : LB P), e ≫ p = 𝟙 X → Smooth p → GeometricallyIntegral p → N.IsLB → ∀ τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ, (∀ (a b : N.ι) (K : Type) [Field K] (h : Sp K ⟶ pullback p j), Set.range (h ≫ pullback.fst p j) ⊆ N.U a → Set.range (h ≫ pullback.fst p j) ⊆ N.U b → valF h _ (τ a).val = valF (h ≫ pullback.fst p j) _ (N.g a b).val * valF h _ (τ b).val) → (∀ a, ∃ u : Γ(X, e ⁻¹ᵁ N.U a)ˣ, ∀ h : Sp Ω ⟶ pullback p j, h ≫ pullback.fst p j = j ≫ e → Set.range (j ≫ e) ⊆ N.U a → valF h _ (τ a).val = valF j _ u.val) → ∃ σ : ∀ a, Γ(P, N.U a)ˣ, ∀ (a : N.ι) (K : Type) [Field K] (h : Sp K ⟶ pullback p j), Set.range (h ≫ pullback.fst p j) ⊆ N.U a → valF (h ≫ pullback.fst p j) _ (σ a).val = valF h _ (τ a).val := by
  intro X P _ Ω _ j hX _ _ _ p e N he _ _ hN τ H₁ H₂
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : QuasiCompact j := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have := DvrModel.isIntegral_of_geometricallyIntegral (IsPullback.of_hasPullback p j)
  have hτ : Compat N (pullback.fst p j) τ := compat_of_valF H₁
  choose ρ hρ using H₂
  let eU : Sp Ω ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 _) (by simp [he])
  have w : eU ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU ≫ pullback.snd p j = 𝟙 _ := pullback.lift_snd _ _ _
  have hτρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ Sp Ω) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a) := by
    intro Z κ z a ha
    have hle : j ⁻¹ᵁ e ⁻¹ᵁ N.U a ≤ eU ⁻¹ᵁ pullback.fst p j ⁻¹ᵁ N.U a := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
    have h₁ : ⊤ ≤ (𝟙 (Sp Ω) :) ⁻¹ᵁ j ⁻¹ᵁ e ⁻¹ᵁ N.U a := fun o _ ↦
      show e (j o) ∈ N.U a from Subsingleton.elim (κ z) o ▸ ha
    have key : res hle (pullU eU _ (τ a)) = pullU j _ (ρ a) := by
      refine Units.ext (eq_of_valR_eq fun x hx ↦ ⟨Ω, inferInstance, 𝟙 _,
        fun o ↦ Subsingleton.elim _ _, ?_⟩)
      have := hρ a eU w (by rintro _ ⟨o, rfl⟩; exact h₁ (x := o) trivial)
      rw [Points.valF_eq_valR, Points.valF_eq_valR] at this
      refine (Points.valR_res _ hle h₁ _).trans ?_
      refine (Points.valR_comp (𝟙 _) eU _ _).symm.trans ?_
      refine Eq.trans ?_ (Points.valR_comp (𝟙 _) j _ _)
      rwa [Category.id_comp, Category.id_comp]
    have := congrArg (gm κ z _) key
    rwa [gm_res_pullU κ eU z hle ha, gm_pull κ j z _ ha] at this
  have key : ∀ a, ∀ y ∈ N.U a, Order.coheight y ≤ 1 → y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  refine ⟨fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩, fun a K _ h _ ↦ ?_⟩
  rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_comp]
  exact congrArg _ (hs a)

end GlobalTheory.GenericExtend

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadOfTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem isLocalHom_of_map_maximalIdeal {W κ : Type} [CommRing W] [IsLocalRing W] [Field κ] (c : W →+* κ)
    (hc : ∀ x ∈ maximalIdeal W, c x = 0) : IsLocalHom c :=
  ⟨fun a ha => by
    by_contra h
    have hm : a ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal a).2 h
    rw [hc a hm] at ha
    exact not_isUnit_zero ha⟩

theorem exists_common_residue {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] [CommRing V]
    [IsLocalRing V] (ψ : R →+* W) [IsLocalHom ψ] (g : R →+* V) [IsLocalHom g] :
    ∃ (κ : Type) (_ : Field κ) (c : W →+* κ) (b : V →+* κ), (∀ x ∈ maximalIdeal W, c x = 0) ∧
      (∀ x ∈ maximalIdeal V, b x = 0) ∧ c.comp ψ = b.comp g := by
  letI : Algebra (ResidueField R) (ResidueField W) := (ResidueField.map ψ).toAlgebra
  letI : Algebra (ResidueField R) (ResidueField V) := (ResidueField.map g).toAlgebra
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (ResidueField W ⊗[ResidueField R] ResidueField V)
  letI := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  refine ⟨_ ⧸ M, inferInstance, q.comp ((Algebra.TensorProduct.includeLeftRingHom).comp (residue W)),
    q.comp ((Algebra.TensorProduct.includeRight.toRingHom).comp (residue V)), fun x hx => ?_, fun x hx => ?_,
    RingHom.ext fun r => ?_⟩
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp only [RingHom.comp_apply]
    congr 1
    rw [← ResidueField.map_residue ψ r, ← ResidueField.map_residue g r]
    change Algebra.TensorProduct.includeLeftRingHom (algebraMap (ResidueField R) (ResidueField W) (residue R r)) =
      Algebra.TensorProduct.includeRight (algebraMap (ResidueField R) (ResidueField V) (residue R r))
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem spread₂_of_trait {B : Scheme.{0}} (H : Over B) [GrpObj H]
    {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {D₁ : DegData V₁ (maximalIdeal V₁)}
    {A₁ : PolAV (Sp (FractionRing V₁))} {G₁ : Over (Sp V₁)} [GrpObj G₁] [IsCommMonObj G₁]
    {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {D₂ : DegData V₂ (maximalIdeal V₂)}
    {A₂ : PolAV (Sp (FractionRing V₂))} {G₂ : Over (Sp V₂)} [GrpObj G₂] [IsCommMonObj G₂]
    (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left)
    (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left)
    {R : Type} [CommRing R] [IsLocalRing R] (ιB : Sp R ⟶ B) (HR : Over (Sp R)) [GrpObj HR] [IsCommMonObj HR]
    (φR : HR.left ⟶ H.left) (hR : IsGrpPullback HR H ιB φR)
    (g₁ : R →+* V₁) (β₁' : G₁.left ⟶ HR.left) (eβ₁ : β₁' ≫ φR = β₁) (hξ₁ : spMap g₁ ≫ ιB = ξ₁)
    (g₂ : R →+* V₂) (hg₂ : IsLocalHom g₂) (β₂' : G₂.left ⟶ HR.left) (hβ₂ : IsGrpPullback G₂ HR (spMap g₂) β₂')
    (eβ₂ : β₂' ≫ φR = β₂) (hξ₂ : spMap g₂ ≫ ιB = ξ₂)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ψ₀ : R →+* W) (hψ : IsLocalHom ψ₀)
    (Ω : Type) [Field Ω] (α : W →+* Ω) (hα : Function.Injective α) (b₁ : V₁ →+* Ω)
    (hb₁ : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0) (eα : α.comp ψ₀ = b₁.comp g₁)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ ((Over.pullback (spMap ψ₀)).obj HR).left)
    (hn : IsGrpPullback GΩ ((Over.pullback (spMap ψ₀)).obj HR) (spMap α) n)
    (n₁ : GΩ.left ⟶ G₁.left) (hn₁ : IsGrpPullback GΩ G₁ (spMap b₁) n₁)
    (hnn : n ≫ pullback.fst HR.hom (spMap ψ₀) = n₁ ≫ β₁')
    (j : splitTorus (Sp W) D₁.toPre.X ⟶ (Over.pullback (spMap ψ₀)).obj HR) (hj : IsMonHom j)
    (ej : GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb₁ hn₁) :
    ∃ ρ, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  haveI := hψ
  haveI := hg₂
  haveI := hj
  obtain ⟨κ, _, c, b₂, hc0, hb0, ec⟩ := exists_common_residue ψ₀ g₂
  have hcl : IsLocalHom c := isLocalHom_of_map_maximalIdeal c hc0
  have hb₂ := GlobalTheory.TorusPart.map_pow_one_eq_zero hb0
  have hW := isGrpPullback_pullback HR (spMap ψ₀)
  have hm := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap c)
  obtain ⟨m₂, hm₂, em₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₂ (spMap b₂)
    ((hm.comp hW).congr ((GlobalTheory.SpreadTrait.spMap_comp' ψ₀ c).trans
      ((congrArg spMap ec).trans (GlobalTheory.SpreadTrait.spMap_comp' g₂ b₂).symm)) rfl)
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₂.gt 0) hb₂ hm₂).2 _
    (GlobalTheory.TorusPart.pullTorus hm j) inferInstance
  refine ⟨ρ, W, inferInstance, inferInstance, inferInstance, spMap ψ₀ ≫ ιB, (Over.pullback (spMap ψ₀)).obj HR,
    inferInstance, inferInstance, pullback.fst HR.hom (spMap ψ₀) ≫ φR, j, Ω, inferInstance, α, b₁, hb₁, GΩ,
    inferInstance, n, hn, n₁, hn₁, κ, inferInstance, c, b₂, hb₂, _, inferInstance, _, hm, m₂, hm₂, hW.comp hR, hj, hα,
    hcl, ?_, ?_, ?_, ?_, ej, hρ⟩
  · rw [← hξ₁, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', eα]
  · rw [← hξ₂, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', ec]
  · rw [← Category.assoc, hnn, Category.assoc, eβ₁]
  · rw [← eβ₂, ← Category.assoc m₂, em₂, Category.assoc]

theorem exists_spread₂ : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → IsIntegral B → IsLocallyNoetherian B → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → ∃ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ hBi hBn hsp
  haveI := hBi
  haveI := hBn
  let R : Type := B.presheaf.stalk (ξ₂ (closedPoint V₂))
  let ιB : Sp R ⟶ B := B.fromSpecStalk (ξ₂ (closedPoint V₂))
  let HR := (Over.pullback ιB).obj H
  have hHR : IsSemiAbelian HR := IsSemiAbelian.pullback ιB H hH
  haveI : IsCommMonObj HR := hHR.comm
  have hR := isGrpPullback_pullback H ιB
  let g₁ : R →+* V₁ := (B.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ₁).hom
  let g₂ : R →+* V₂ := (Scheme.stalkClosedPointTo ξ₂).hom
  have hg₂ : IsLocalHom g₂ := Scheme.isLocalHom_stalkClosedPointTo' ξ₂
  have hξ₁ : spMap g₁ ≫ ιB = ξ₁ := by
    have e : spMap g₁ = Spec.map (Scheme.stalkClosedPointTo ξ₁) ≫ Spec.map (B.presheaf.stalkSpecializes hsp) := by
      rw [← Spec.map_comp]; rfl
    rw [e, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hξ₂ : spMap g₂ ≫ ιB = ξ₂ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₂
  obtain ⟨β₁', hβ₁', eβ₁⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₁) (hβ₁.congr hξ₁.symm rfl)
  obtain ⟨β₂', hβ₂', eβ₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₂) (hβ₂.congr hξ₂.symm rfl)
  by_cases hl : IsLocalHom g₁
  · haveI := hl
    let κ₁ := ResidueField V₁
    have hC : IsLocalHom (PowerSeries.C (R := κ₁)) :=
      ⟨fun a ha => by simpa using ha.map (PowerSeries.constantCoeff (R := κ₁))⟩
    let c₁ : V₁ →+* PowerSeries κ₁ := (PowerSeries.C (R := κ₁)).comp (residue V₁)
    have hcl : IsLocalHom c₁ := RingHom.isLocalHom_comp _ _
    let ψ₀ : R →+* PowerSeries κ₁ := c₁.comp g₁
    have hψ : IsLocalHom ψ₀ := RingHom.isLocalHom_comp _ _
    let α := algebraMap (PowerSeries κ₁) (FractionRing (PowerSeries κ₁))
    have hα : Function.Injective α := IsFractionRing.injective _ _
    let b₁ : V₁ →+* FractionRing (PowerSeries κ₁) := α.comp c₁
    have hc0 : ∀ x ∈ maximalIdeal V₁, c₁ x = 0 := fun x hx => by
      simp [c₁, (IsLocalRing.residue_eq_zero_iff x).2 hx]
    have hc : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), c₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hc0
    have hb : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := fun x hx => by
      simp [b₁, hc x hx]
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    obtain ⟨mc, hmc, hmcβ⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₁' (spMap c₁)
      (hm₁.congr (GlobalTheory.SpreadTrait.spMap_comp' g₁ c₁).symm rfl)
    have hn := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap α)
    have hn' : IsGrpPullback _ G₁ (spMap b₁) _ := (hn.comp hmc).congr (GlobalTheory.SpreadTrait.spMap_comp' c₁ α) rfl
    have hnn : pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ pullback.fst HR.hom (spMap ψ₀) =
        (pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ mc) ≫ β₁' := by
      rw [Category.assoc, hmcβ]
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      (PowerSeries κ₁) ψ₀ hψ _ α hα b₁ hb rfl _ _ hn _ hn' hnn
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hc hmc) inferInstance
      (GlobalTheory.TorusPart.pullTorus_gtTorus (U₁.gt 0) hc hb hmc hn' hn rfl rfl)
  · obtain ⟨W, _, _, _, ψ₀, Ω, _, αK, b₁, hψ, hb, eα, hT⟩ := GlobalTheory.T.exists_trait_nonlocal_torusExtension' R HR hHR V₁ g₁ hl
    haveI := hψ
    let alg := algebraMap W (FractionRing W)
    have hα : Function.Injective (αK.comp alg) :=
      αK.injective.comp (IsFractionRing.injective W (FractionRing W))
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    have hG₁' : IsSemiAbelian ((Over.pullback (spMap ψ₀)).obj HR) := IsSemiAbelian.pullback _ HR hHR
    obtain ⟨φ₁, hφ₁, -⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap alg)
      ((isGrpPullback_pullback HR (spMap (alg.comp ψ₀))).congr (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ alg).symm rfl)
    have hn' := isGrpPullback_pullback G₁ (spMap b₁)
    obtain ⟨n, hn, hnm⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap (αK.comp alg))
      ((hn'.comp hβ₁').congr ((GlobalTheory.SpreadTrait.spMap_comp' g₁ b₁).trans ((congrArg spMap eα.symm).trans
        (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ (αK.comp alg)).symm)) rfl)
    have hb' : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hb
    obtain ⟨j, hj, ej⟩ := GlobalTheory.T.extend_splitTorus_hom_over_dvr W ((Over.pullback (spMap ψ₀)).obj HR) hG₁' _ φ₁ hφ₁ hT Ω αK _ n hn _
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb' hn') inferInstance
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      W ψ₀ hψ Ω (αK.comp alg) hα b₁ hb' eα _ n hn _ hn' hnm j hj ej

end GlobalTheory.Poinc.Sep.Spz

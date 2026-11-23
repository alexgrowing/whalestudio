import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RangeSubsetOfForallField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftMulHomPullbackFst

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MultiplicativeReduction

open GlobalTheory.WeierstrassCurve

theorem isProper_pullback_snd {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P)
    {K : Type} [Field K] (f : R →+* K) (hΔ : f W.Δ ≠ 0) :
    IsProper (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f))) := by
  have hpb : IsPullback (mapHom W f rfl ∣_ U) ((mapHom W f rfl ⁻¹ᵁ U).ι ≫ toSpec (W.map f))
      (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
    (isPullback_morphismRestrict (mapHom W f rfl) U).paste_vert (isPullback_mapHom W f rfl)
  have htop : mapHom W f rfl ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    let k := (scheme (W.map f)).residueField x
    obtain ⟨ρ, P, h, hx⟩ : ∃ (ρ : K →+* k) (P : Fin 3 → k)
        (h : IsUnimodularSol ((W.map f).map ρ) P),
        (scheme (W.map f)).fromSpecResidueField x = ptHom (W.map f) ρ P h := by
      obtain ⟨g, hg⟩ := Spec.map_surjective
        ((scheme (W.map f)).fromSpecResidueField x ≫ toSpec (W.map f))
      exact ⟨g.hom, exists_eq_ptHom (W.map f) (A := k) g.hom _ hg.symm⟩
    have hE : ((W.map f).map ρ).IsElliptic := ⟨by
      rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]
      exact (IsUnit.mk0 _ hΔ).map ρ⟩
    have h1 := (hU k (ρ.comp f) P (h.comp_of_map_eq rfl)).mpr h.nonsingular
    rw [← ptHom_mapHom W f rfl ρ P h, Scheme.Hom.comp_preimage, ← hx] at h1
    have h2 : (scheme (W.map f)).fromSpecResidueField x (IsLocalRing.closedPoint k) ∈
        mapHom W f rfl ⁻¹ᵁ U := h1 (Set.mem_univ (IsLocalRing.closedPoint k))
    have h3 : (scheme (W.map f)).fromSpecResidueField x (IsLocalRing.closedPoint k) = x :=
      Scheme.fromSpecResidueField_apply x _
    exact h3 ▸ h2
  have : IsIso (mapHom W f rfl ⁻¹ᵁ U).ι := by
    rw [htop]; exact inferInstanceAs (IsIso (Scheme.topIso _).hom)
  rw [← hpb.isoPullback_inv_snd]
  infer_instance

theorem nonempty_torusExtension_splitTorus (K : Type) [Field K] :
    Nonempty (TorusExtension (splitTorus (Spec (CommRingCat.of K)) ℤ)) :=
  ⟨Geo.Tor.torusExtOfIso (GlobalTheory.Diag.baseChangeIso (𝟙 (Spec (CommRingCat.of K))) ℤ)
    (GlobalTheory.Diag.torusExtension _ ℤ (𝟙 _))⟩

theorem isSemiAbelian_and_specialFibre : ∀ (W : WeierstrassCurve (PowerSeries ℚ)), W = ⟨1, 0, 0, PowerSeries.X, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : (PowerSeries ℚ) →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → QuasiCompact (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))] [IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : (PowerSeries ℚ) →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → IsSemiAbelian (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ ∃ i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField (PowerSeries ℚ)))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries ℚ))))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro W hW U hU hsm hgi hqc _ _ hmul
  have hgc : GeometricallyConnected (U.ι ≫ toSpec W) := by
    refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
    have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    exact inferInstanceAs (ConnectedSpace Z)
  have htor : ∀ (K : Type) [Field K] (f : PowerSeries ℚ →+* K), f PowerSeries.X = 0 →
      ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ toSpec W)),
        IsMonHom i.hom := by
    intro K _ f hf
    obtain ⟨U', _, e, he, -, hU', hmul'⟩ :=
      GlobalTheory.SmoothLocusBaseChange.main _ K f W U hU hsm hgi hmul
    have hl : U'.ι ≫ toSpec (W.map f) =
        e.hom.left ≫ pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
      (Over.w e.hom).symm
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    obtain ⟨i, hi⟩ := GlobalTheory.NodalCubic.exists_splitTorus_iso K (W.map f)
      (by subst hW; ext <;> simp [hf]) U' hU' (by rw [hl]; infer_instance)
      (by
        rw [hl]
        exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
          (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨(Category.comp_id _).symm⟩)
          (inferInstanceAs (GeometricallyIntegral
            (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)))))) hmul'
    exact ⟨i ≪≫ e, by rw [Iso.trans_hom]; infer_instance⟩
  refine ⟨⟨inferInstance, hsm, inferInstanceAs (IsSeparated (U.ι ≫ toSpec W)), hqc,
    hgc, fun Ω _ _ p => ?_⟩,
    htor _ _ ?_⟩
  · obtain ⟨g, rfl⟩ := Spec.map_surjective p
    obtain ⟨f, rfl⟩ : ∃ f : PowerSeries ℚ →+* Ω, g = CommRingCat.ofHom f := ⟨g.hom, rfl⟩
    by_cases hf : f PowerSeries.X = 0
    · obtain ⟨i, hi⟩ := htor Ω f hf
      obtain ⟨T⟩ := nonempty_torusExtension_splitTorus Ω
      exact ⟨Geo.Tor.torusExtOfIso i T⟩
    · have hΔ : W.Δ = PowerSeries.X ^ 2 * (1 - 64 * PowerSeries.X) := by
        subst hW
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        ring
      have hu : IsUnit (1 - 64 * PowerSeries.X : PowerSeries ℚ) := by
        rw [PowerSeries.isUnit_iff_constantCoeff]
        simp
      have hΔ' : f W.Δ ≠ 0 := by
        rw [hΔ, map_mul, map_pow]
        exact mul_ne_zero (pow_ne_zero _ hf) (hu.map f).ne_zero
      refine ⟨GlobalTheory.torusExtensionOfAbelian _ ⟨inferInstance, ?_, ?_, ?_⟩⟩
      · exact inferInstanceAs (Smooth (pullback.snd (U.ι ≫ toSpec W) _))
      · exact isProper_pullback_snd W U hU f hΔ'
      · exact inferInstanceAs (GeometricallyConnected (pullback.snd (U.ι ≫ toSpec W) _))
  · rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff]
    simp

end GlobalTheory.MultiplicativeReduction

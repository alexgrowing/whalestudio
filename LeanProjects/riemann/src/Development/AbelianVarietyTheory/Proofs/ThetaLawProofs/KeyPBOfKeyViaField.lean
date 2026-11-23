import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyDesc

open GlobalTheory.KeyCancel

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMapR_algebraMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    Chart.dualMapR f (algebraMap A _ a) = algebraMap B _ (f a) := by
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMapR_eps {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Chart.dualMapR f DualNumber.eps = DualNumber.eps := by
  ext <;> simp [Chart.dualMapR]

theorem keyPB_of_keyVia_field : ∀ (R k K : Type) [CommRing R] [Field k] [Field K] (α : R →+* k) (β : k →+* K)
    (y : KeyIn R) (z : KeyIn k) (x : KeyIn K) (φ : x.P.A.left ⟶ z.P.A.left) (w₀ : LB.Iso x.P.L (z.P.L.pull φ))
    (ψ : z.P.A.left ⟶ y.P.A.left) (w₁ : LB.Iso x.P.L (y.P.L.pull (φ ≫ ψ))), KeyVia x z β φ w₀ →
    KeyVia x y (β.comp α) (φ ≫ ψ) w₁ → IsGrpPullback z.P.A y.P.A (spMap α) ψ → LBIso z.P.L (y.P.L.pull ψ) →
    KeyPB z y α := by
  intro R k K _ _ _ α β y z x φ w₀ ψ w₁ ⟨he₀, hg₀, F₀, hc₀, hw₀, hr₀, hs₀, hF₀, hFe₀, hv₀⟩
    ⟨he₁, hg₁, F₁, hc₁, hw₁, hr₁, hs₁, hF₁, hFe₁, hv₁⟩ hψ ⟨u, hu⟩
  have he : eSec z.P.A ≫ ψ = spMap α ≫ eSec y.P.A := PolBaseChange.eSec_comm hψ
  obtain ⟨w, g, m⟩ := KeyPow.exists_rescale y.P.isLB z.P.isLB ((isGen_iff u).1 hu) (p := z.P.A.hom)
    (Over.w η[z.P.A]) he z.rig_gen y.rig_gen
  have g₀ := (isGen_iff w₀).1 hw₀
  obtain ⟨w₂, T⟩ := exists_comp z.P.isLB w w₀ g g₀ y.P.isLB x.P.isLB
  have r₀ := (maps_iff w₀ _ (fun _ => eSec z.P.A) _ x.rig z.rig (spMap β) _ (rigPull_le φ (spMap β) he₀ z.P.L)
    (fun _ => rfl)).1 hr₀
  have r₂ := T.pmaps_comp z.P.isLB (fun _ => he₀) m r₀
  rw [← spMap_comp] at r₂
  obtain rfl : w₂ = w₁ := rigidified_iso_unique globalFns_holds x.P y.P.isLB (φ ≫ ψ) w₂ w₁
    ((isGen_iff _).2 (T.pgen_comp z.P.isLB g g₀)) hw₁ x.rig _
    ((maps_iff w₂ _ (fun _ => eSec y.P.A) _ x.rig y.rig (spMap (β.comp α)) _
      (rigPull_le (φ ≫ ψ) (spMap (β.comp α)) he₁ y.P.L) (fun _ => rfl)).2 r₂) hr₁
  have := z.P.isAb.smooth
  have := y.P.isAb.proper
  have : IsSchemeTheoreticallyDominant (spMap β) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom β) β.injective
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hc₀.1.flip
  have : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact) hc₀.1.flip inferInstance
  obtain rfl : F₀ = Chart.dualMapR β := dualNumber_ringHom_ext
    (fun a => (hF₀ a).trans (dualMapR_algebraMap β a).symm) (hFe₀.trans (dualMapR_eps β).symm)
  obtain rfl : F₁ = (Chart.dualMapR β).comp (Chart.dualMapR α) := dualNumber_ringHom_ext
    (fun a => by rw [hF₁, RingHom.comp_apply, RingHom.comp_apply, dualMapR_algebraMap, dualMapR_algebraMap])
    (by rw [hFe₁, RingHom.comp_apply, dualMapR_eps, dualMapR_eps])
  refine ⟨ψ, he, w, hg₀.symm.trans hg₁, Chart.dualMapR α, hψ, (isGen_iff w).2 g,
    (maps_iff w _ (fun _ => eSec y.P.A) _ z.rig y.rig (spMap α) _ (rigPull_le ψ (spMap α) he y.P.L)
      (fun _ => rfl)).2 m, fun j i hle => φ.app_injective _ (fn_ext fun q hq => ?_), dualMapR_algebraMap α,
    dualMapR_eps α, fun i => ?_⟩
  · have hq' : φ ((𝟙 x.P.A.left : _ ⟶ _) q) ∈ (y.P.L.pull ψ).U j ⊓ z.P.L.U i := hq
    obtain ⟨l, hl⟩ := exists_chart x.P.isLB q
    have a := (appLE_eq_iff_stalk w₀ z.th x.th).1 hs₀ _ (𝟙 _) q i l hq'.2 hl
    have b := (appLE_eq_iff_stalk w₂ y.th x.th).1 hs₁ _ (𝟙 _) q (j PUnit.unit) l ((mem_pull (F := ψ)).1 hq'.1) hl
    rw [T _ (𝟙 _) q (j PUnit.unit) i l (mem_pull.1 hq'.1) hq'.2 hl, Units.val_mul, _root_.mul_assoc, ← a,
      ← Category.assoc] at b
    refine (gs_pull (𝟙 _) φ q _ hq' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) φ q _ hq' _).symm)
    refine (gs_appLE ψ _ _ hle (𝟙 _ ≫ φ) q hq' _).trans (b.trans ?_)
    rw [gs_mul (𝟙 _ ≫ φ) q _ hq', gs_res (𝟙 _ ≫ φ) q _ hq']
    exact congrArg (· * _) (gs_unit (𝟙 _ ≫ φ) q _ hq' _).symm
  · refine Spread.tangent_ext β β.injective y.P.A.hom ?_ ?_
    · rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext fun a => (dualMapR_algebraMap α a).symm
    · have a := hv₀ (i.cast hg₀.symm)
      have b := hv₁ (i.cast hg₀.symm)
      rw [← Category.assoc, a, spMap_comp, Category.assoc, Category.assoc] at b
      exact b

end GlobalTheory.KeyDesc

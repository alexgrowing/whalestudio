import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFamIsometryInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelationStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF

open IntCoord in

theorem diff_mem_eigLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} {f : P.A ⟶ P'.A}
    (hf : ∀ x, a.act x ≫ f = f ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : F.IsDiffOf F' f M) (τ : O →+* 𝓞 K) {c : Fin F.P₀.g → K} (hc : c ∈ F.eigLat a τ) :
    M c ∈ F'.eigLat a' τ := by
  obtain ⟨u, hu, he⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.2 O a τ c).1 hc
  refine Submodule.subset_span ⟨u ≫ f, hM u c hu, fun x => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (he x),
    Category.assoc]

theorem map_eigLat_of_iso {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} (e : P.A ≅ P'.A)
    (hf : ∀ x, a.act x ≫ e.hom = e.hom ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    {M' : (Fin F'.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)}
    (hM : F.IsDiffOf F' e.hom M) (hM' : F'.IsDiffOf F e.inv M') (τ : O →+* 𝓞 K) :
    (F.eigLat a τ).map (M.restrictScalars (𝓞 K)) = F'.eigLat a' τ := by
  refine le_antisymm ?_ fun c hc => ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact diff_mem_eigLat hf hM τ hc
  · have hf' : ∀ x, a'.act x ≫ e.inv = e.inv ≫ a.act x := fun x => by
      rw [Iso.comp_inv_eq, Category.assoc, hf, Iso.inv_hom_id_assoc]
    refine ⟨M' c, diff_mem_eigLat hf' hM' τ hc, ?_⟩
    obtain ⟨u, hu, -⟩ := ((integral_tangent_coordinates K P' F').2.2.2.2.2 O a' τ c).1 hc
    have h2 := hM _ _ (hM' _ _ hu)
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2
    exact ((integral_tangent_coordinates K P' F').1 u hu.1).unique h2 hu

theorem deg_eigLat_eq_of_iso : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (O : Type) [CommRing O] (a : OAct O P.A) (a' : OAct O P'.A) (e : P.A ≅ P'.A), F.IsHerm h → F'.IsHerm h' → Serre.IsLinearHom a a' e.hom → LamEq P'.L e.hom e.hom P.L (𝟙 P.A) (𝟙 P.A) → ∀ τ : O →+* 𝓞 K, deg h (F.eigLat a τ) = deg h' (F'.eigLat a' τ) := by
  intro hT hL K _ _ P P' F F' h h' O _ a a' e hh hh' hlin hlam τ
  have hm : IsMonHom e.hom := hlin.1
  have hm' : IsMonHom e.inv := inferInstance
  obtain ⟨M, hM, -⟩ := (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' e.hom hm).1
  obtain ⟨M', hM', -⟩ := (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P' F' P F e.inv hm').1
  have hid : F.IsDiffOf F (𝟙 P.A) LinearMap.id := fun u c hu => by simpa using hu
  have hiso := GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hT hL K P F P' F' h h' e.hom (𝟙 P.A) M LinearMap.id hh hh' hm inferInstance hlam hM hid
  have hle : F.eigLat a τ ≤ F.lieLat := Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩
  have hfg : (F.eigLat a τ).FG := (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1.of_le hle
  rw [← map_eigLat_of_iso e hlin.2 hM hM' τ]
  exact (deg_map_isometry K _ _ h h' M _ hfg hiso).symm

end GlobalTheory.LamF

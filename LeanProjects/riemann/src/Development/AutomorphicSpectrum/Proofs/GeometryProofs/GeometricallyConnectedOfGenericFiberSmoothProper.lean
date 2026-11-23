import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfCommGroupNsmulSurjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeNsmulSurjectiveStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem dense_range_fst_generic (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{0}} (p : X ⟶ Sp R) (hp : IsOpenMap p) :
    Dense (Set.range (pullback.fst p (spMap (algebraMap R K)))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let y : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hy : ∀ z : PrimeSpectrum R, PrimeSpectrum.comap (algebraMap R K) y ⤳ z := by
    intro z
    rw [← PrimeSpectrum.le_iff_specializes]
    intro a ha
    have h0 : algebraMap R K a = 0 := ha
    have : a = 0 := hinj (by rw [h0, map_zero])
    rw [this]
    exact z.asIdeal.zero_mem
  have hyy : (spMap (algebraMap R K)) y = PrimeSpectrum.comap (algebraMap R K) y := rfl
  rw [Scheme.Pullback.range_fst, dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  have hmem : (spMap (algebraMap R K)) y ∈ p '' U := by
    rw [hyy]
    exact (hy (p x)).mem_open (hp U hU) ⟨x, hx, rfl⟩
  obtain ⟨x', hx'U, hx'⟩ := hmem
  exact ⟨x', hx'U, ⟨y, hx'.symm⟩⟩

theorem geometricallyConnected_of_generic : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap R K))) → GeometricallyConnected G.hom := by
  intro R K _ _ _ _ _ G _ _ hsm hpr hgc
  set f := spMap (algebraMap R K) with hf
  let F := Over.pullback f
  let GK := F.obj G
  have hab : IsAbelianScheme GK := by
    refine IsAbelianScheme.mk inferInstance ?_ ?_ hgc
    · show Smooth (pullback.snd G.hom f)
      infer_instance
    · show IsProper (pullback.snd G.hom f)
      infer_instance
  refine GlobalTheory.T.geometricallyConnected_of_commGroup_nsmul_surjective (Sp R) G inferInstance inferInstance ?_
  intro n hn
  have hK := GlobalTheory.T.abelianScheme_nsmul_surjective K GK hab n hn
  have hmap : F.map (𝟙 G ^ n) = 𝟙 GK ^ n := by
    rw [← F.map_id]
    exact (Functor.homMonoidHom F (X := G) (M := G)).map_pow _ n
  set φ := (𝟙 G ^ n).left with hφ
  have hsq : (𝟙 GK ^ n).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ φ := by
    rw [← hmap]
    simp [F, φ] <;> exact pullback.lift_fst _ _ _
  have hw : φ ≫ G.hom = G.hom := Over.w (𝟙 G ^ n)
  have hcomp : IsProper (φ ≫ G.hom) := by rw [hw]; exact hpr
  have hsep : IsSeparated G.hom := inferInstance
  have hprop : UniversallyClosed φ := by
    first
    | exact (MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated) φ G.hom hsep hcomp).toUniversallyClosed
    | exact MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated) φ G.hom hsep inferInstance
    | exact UniversallyClosed.of_comp_of_isSeparated φ G.hom
    | exact (IsProper.of_comp φ G.hom).toUniversallyClosed
  have hcl : IsClosed (Set.range φ) := φ.isClosedMap.isClosed_range
  have hop : IsOpenMap G.hom := G.hom.isOpenMap
  have hdense := dense_range_fst_generic R K G.hom hop
  have hsub : Set.range (pullback.fst G.hom f) ⊆ Set.range φ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := hK.surj z
    refine ⟨pullback.fst G.hom f w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have huniv : Set.range φ = Set.univ :=
    (hdense.mono hsub).closure_eq ▸ hcl.closure_eq.symm
  exact ⟨fun x => by
    have : x ∈ Set.range φ := huniv ▸ Set.mem_univ x
    exact this⟩

end GlobalTheory.CompanionTheory.Ar.Approx

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GeometricallyConnectedOfClosedFibre

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GenSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.ConnFibre

theorem exists_geometricallyConnected : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → Smooth f → GlobalTheory.AbLaw.IsProjBy f → GeometricallyConnected f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → GeometricallyConnected f' := by
  intro R K _ _ _ _ _ _ X X₀ f f₀ φ hb hs hp hc
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hs hp _ (Inh.trivLB_isLB _)
  have hpr : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R X f hp
  let L := AlgebraicClosure K
  let g₀ : R →+* L := (algebraMap K L).comp (algebraMap R K)
  have hg₀ : Function.Injective g₀ := (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  let y₀ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  have h₀ : IsPullback (pullback.fst f₀ y₀ ≫ φ) (pullback.snd f₀ y₀) f
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback f₀ y₀).paste_horiz hb
    erw [← Spec.map_comp] at this
    exact this
  have hs₀ : Smooth f₀ := MorphismProperty.of_isPullback hb hs
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ f₀ hs₀ hc
  have hint : IsIntegral (pullback f₀ y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback f₀ y₀)
  have hpr₀ : IsProper (pullback.snd f₀ y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback f₀ y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst f₀ y₀ ≫ φ) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  have hsurj : Surjective f := by
    have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hbot : (⊥ : PrimeSpectrum R) ∈ Set.range f := by
      refine ⟨(pullback.fst f₀ y₀ ≫ φ) x₀, ?_⟩
      have e : f ((pullback.fst f₀ y₀ ≫ φ) x₀) =
          Spec.map (CommRingCat.ofHom g₀) (pullback.snd f₀ y₀ x₀) := congrArg (fun t => t x₀) h₀.w
      refine e.trans (PrimeSpectrum.ext (le_bot_iff.1 fun a ha => ?_))
      have ha' : g₀ a ∈ (pullback.snd f₀ y₀ x₀).asIdeal := ha
      by_contra hne
      have hne' : g₀ a ≠ 0 := fun h => hne (hg₀ (h.trans (map_zero g₀).symm))
      exact (PrimeSpectrum.isPrime (pullback.snd f₀ y₀ x₀)).ne_top
        (Ideal.eq_top_of_isUnit_mem _ ha' (IsUnit.mk0 _ hne'))
    refine ⟨fun z => ?_⟩
    have hsp : (⊥ : PrimeSpectrum R) ⤳ (z : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact hsp.mem_closed hcl hbot
  refine ⟨δ, fun h => hδ (h ▸ map_zero g₀), fun R' _ g hg X' π f' hπ => ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩
  have h' : IsPullback (fst ≫ π) snd f (Spec.map (CommRingCat.ofHom ((algebraMap R' F).comp g))) := by
    have := h.paste_horiz hπ
    erw [← Spec.map_comp] at this
    exact this
  have : Surjective snd := MorphismProperty.of_isPullback h' hsurj
  obtain ⟨z, -⟩ := snd.surjective (⊥ : PrimeSpectrum F)
  have := preconnectedSpace_of_line P h' _ (hker F _ (hg.map (algebraMap R' F)))
  exact ⟨⟨z⟩⟩

end GlobalTheory.GenSpread

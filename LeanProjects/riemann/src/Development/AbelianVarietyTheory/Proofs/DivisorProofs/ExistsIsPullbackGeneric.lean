import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.GenericFibreChart

theorem isPullback_of_fac_mono {C : Type*} [Category C] {P V G S T : C} {p : P ⟶ G} {q : P ⟶ T}
    {h : G ⟶ S} {j : T ⟶ S} (H : IsPullback p q h j) (i : V ⟶ G) [Mono i] (l : P ⟶ V)
    (hl : l ≫ i = p) : IsPullback l q (i ≫ h) j := by
  have w : l ≫ i ≫ h = q ≫ j := by rw [← Category.assoc, hl, H.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => H.lift (s.fst ≫ i) s.snd (by rw [Category.assoc]; exact s.condition)) ?_ ?_ ?_⟩⟩
  · intro s
    rw [← cancel_mono i, Category.assoc, hl, H.lift_fst]
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h1 h2
    apply H.hom_ext
    · rw [H.lift_fst, ← h1, Category.assoc, hl]
    · rw [H.lift_snd, h2]

theorem isPullback_of_comp_mono {C : Type*} [Category C] {P X Y W Z : C} {p : P ⟶ X} {q : P ⟶ Y}
    {a : X ⟶ W} {g : Y ⟶ W} (m : W ⟶ Z) [Mono m] (H : IsPullback p q (a ≫ m) (g ≫ m)) :
    IsPullback p q a g := by
  have w : p ≫ a = q ≫ g := by
    rw [← cancel_mono m, Category.assoc, Category.assoc, H.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => H.lift s.fst s.snd (by
      rw [← Category.assoc, ← Category.assoc, s.condition])) ?_ ?_ ?_⟩⟩
  · intro s
    exact H.lift_fst _ _ _
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h1 h2
    apply H.hom_ext
    · rw [H.lift_fst, h1]
    · rw [H.lift_snd, h2]

theorem exists_isPullback_generic :
    ∀ (R₀ : Type) [CommRing R₀] (f : R₀) (A : Over (Sp (Localization.Away f))) (R : Type)
      [CommRing R] [IsDomain R] (ρ : R₀ →+* R), ρ f ≠ 0 →
      ∀ (G : Over (Sp R)) (V : G.left.Opens) (φ : V.toScheme ⟶ A.left),
      (∀ z : G.left, z ∈ V ↔ ρ f ∉ (G.hom z).asIdeal) →
      IsPullback φ (V.ι ≫ G.hom) (A.hom ≫ GlobalTheory.Desc.awayMap f) (spMap ρ) →
      ∃ (g : Sp (FractionRing R) ⟶ Sp (Localization.Away f))
        (l : pullback G.hom (jK R) ⟶ V.toScheme),
        l ≫ V.ι = pullback.fst G.hom (jK R) ∧
          IsPullback (l ≫ φ) (pullback.snd G.hom (jK R)) A.hom g := by
  intro R₀ _ f A R _ _ ρ hf G V φ hV hP
  have hu : IsUnit (((algebraMap R (FractionRing R)).comp ρ) f) := by
    rw [isUnit_iff_ne_zero, RingHom.comp_apply]
    exact fun h => hf ((IsFractionRing.injective R (FractionRing R)) (by rw [h, map_zero]))
  let ψ : Localization.Away f →+* FractionRing R := IsLocalization.Away.lift f hu
  have hψ : ψ.comp (algebraMap R₀ (Localization.Away f)) =
      (algebraMap R (FractionRing R)).comp ρ := IsLocalization.Away.lift_comp f hu
  have hg : spMap ψ ≫ GlobalTheory.Desc.awayMap f = jK R ≫ spMap ρ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
  have hr : Set.range (pullback.fst G.hom (jK R)) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine (hV _).2 ?_
    have hx : G.hom (pullback.fst G.hom (jK R) x) = jK R (pullback.snd G.hom (jK R) x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [hx]
    intro hmem
    have hmem' : algebraMap R (FractionRing R) (ρ f) ∈
        (pullback.snd G.hom (jK R) x : PrimeSpectrum (FractionRing R)).asIdeal := hmem
    exact (pullback.snd G.hom (jK R) x : PrimeSpectrum (FractionRing R)).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem' hu)
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  refine ⟨spMap ψ, IsOpenImmersion.lift V.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have h1 := isPullback_of_fac_mono (IsPullback.of_hasPullback G.hom (jK R)) V.ι
    (IsOpenImmersion.lift V.ι _ hr) (IsOpenImmersion.lift_fac _ _ _)
  have h2 := h1.paste_horiz hP
  refine isPullback_of_comp_mono (GlobalTheory.Desc.awayMap f) ?_
  rw [hg]
  exact h2

end GlobalTheory.GenericFibreChart

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.NearFibreIso

open GlobalTheory.DenseFibreIso

variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)

def Near (Q : MorphismProperty Scheme.{0}) (x : X) : Prop :=
  ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Y) (f' : T' ⟶ T),
    IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f'

theorem Near.of_pullback {Q : MorphismProperty Scheme.{0}} {T T' : Scheme.{0}} {g : T ⟶ X}
    {g' : T' ⟶ Y} {f' : T' ⟶ T} (H : IsPullback f' g' g f) [IsOpenImmersion g] {y : T}
    (h : Near f' Q y) : Near f Q (g y) := by
  obtain ⟨T₀, T₀', g₀, g₀', f₀, H₀, hg₀, ⟨z, rfl⟩, hQ⟩ := h
  have := hg₀
  refine ⟨T₀, T₀', g₀ ≫ g, g₀' ≫ g', f₀, H₀.paste_vert H, inferInstance, ⟨z, ?_⟩, hQ⟩
  simp

theorem isIso_fibre_of_pullback {S : Scheme.{0}} (t : S ⟶ Sp R)
    [IsIso (pullback.snd f (pullback.fst s t))] {T T' : Scheme.{0}} {g : T ⟶ X} {g' : T' ⟶ Y}
    {f' : T' ⟶ T} (H : IsPullback f' g' g f) :
    IsIso (pullback.snd f' (pullback.fst (g ≫ s) t)) := by
  have H' : IsPullback (pullback.snd f' (pullback.fst (g ≫ s) t))
      (pullback.fst f' (pullback.fst (g ≫ s) t) ≫ g') (pullback.fst (g ≫ s) t ≫ g) f :=
    (IsPullback.of_hasPullback _ _).flip.paste_vert H
  refine DenseFibreIso.isIso_of_fibre s f t H' (pullback.snd _ _) ?_
  rw [Category.assoc, pullback.condition]

variable (K : Type) [Field K] [Algebra R K]

theorem near_isFinite [IsProper f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) : Near f @IsFinite x := by
  have hsub : (f ⁻¹' {x}).Subsingleton := by
    let k : Sp K := IsLocalRing.closedPoint K
    have hk : s x = spMap (algebraMap R K) k := by
      apply PrimeSpectrum.ext
      rw [← hx, RingHom.ker_eq_comap_bot, ← Ideal.eq_bot_of_prime k.asIdeal]
      rfl
    obtain ⟨x', hx', -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨z₁, hz₁, hz₁'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₁ x' (hy₁.trans hx'.symm)
    obtain ⟨z₂, hz₂, hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₂ x' (hy₂.trans hx'.symm)
    have hz : z₁ = z₂ :=
      (pullback.snd f (pullback.fst s (spMap (algebraMap R K)))).isOpenEmbedding.injective
        (hz₁'.trans hz₂'.symm)
    rw [← hz₁, ← hz₂, hz]
  obtain ⟨V, hxV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hsub.finite
  refine ⟨V, f ⁻¹ᵁ V, V.ι, (f ⁻¹ᵁ V).ι, f ∣_ V, isPullback_morphismRestrict f V, inferInstance, ?_, hV⟩
  simpa using hxV

theorem near_isClosedImmersion [hfin : IsFinite f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f @IsClosedImmersion x := by
  refine DenseFibreIso.local_of_ring s f @IsClosedImmersion K ?_ x hx
  intro A B _ _ _ _ _ _ j j' _ H _ hbij m
  have hf : IsFinite (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) H.flip hfin
  have : Module.Finite A B := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf)
  obtain ⟨a, ha, hsurj⟩ := DenseFibreIso.exists_away_surjective (A ⊗[R] K) hbij.2 m
  exact ⟨a, ha, IsClosedImmersion.spec_of_surjective _ hsurj⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem near_isIso [hcl : IsClosedImmersion f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  refine DenseFibreIso.local_of_ring s f (MorphismProperty.isomorphisms _) K ?_ x hx
  intro A B _ _ _ _ _ _ j j' hj H hjs hbij m
  have : IsOpenImmersion j' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hj
  have hci : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h1 := (spMap (algebraMap A B)).app_surjective ⊤ (isAffineOpen_top _)
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    intro b
    obtain ⟨c, hc⟩ := h1 ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom c, ?_⟩
    have h3 := congr_arg (fun k => (ConcreteCategory.hom k) c) h2
    simp only [CategoryTheory.comp_apply, CommRingCat.hom_ofHom] at h3
    rw [← h3]
    change (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((spMap (algebraMap A B)).app ⊤ c) = b
    rw [hc]
    simp
  have : IsLocallyNoetherian (Sp A) := isLocallyNoetherian_of_isOpenImmersion j
  have : IsNoetherian (Sp A) := {}
  have : IsNoetherianRing A := isNoetherian_Spec.mp this
  have hflat : Flat (spMap (algebraMap R B)) := by
    have e : spMap (algebraMap R B) = spMap (algebraMap A B) ≫ spMap (algebraMap R A) := by
      change Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rw [e, ← hjs, reassoc_of% H.w]
    infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat)
  obtain ⟨a, ha, hb⟩ := DenseFibreIso.exists_away_bijective R K hs hbij.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.mpr hb⟩

theorem near_isIso_of_isProper [IsProper f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  obtain ⟨T, T', g, g', f', H, hg, ⟨y, rfl⟩, hQ⟩ := near_isFinite s f K x hx
  have := hg
  have : IsFinite f' := hQ
  have : IsIso (pullback.snd f' (pullback.fst (g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback s f _ H
  have hy : RingHom.ker (algebraMap R K) = ((g ≫ s) y).asIdeal := by simpa using hx
  obtain ⟨T₂, T₂', g₂, g₂', f₂, H₂, hg₂, ⟨y₂, rfl⟩, hQ₂⟩ := near_isClosedImmersion (g ≫ s) f' K y hy
  have := hg₂
  have : IsClosedImmersion f₂ := hQ₂
  have : IsIso (pullback.snd f₂ (pullback.fst (g₂ ≫ g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback (g ≫ s) f' _ H₂
  have : IsLocallyNoetherian T₂ := isLocallyNoetherian_of_isOpenImmersion (g₂ ≫ g)
  have : IsOpenImmersion g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hg
  have : IsOpenImmersion g₂' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H₂ hg₂
  have : Flat (f₂ ≫ g₂ ≫ g ≫ s) := by
    rw [reassoc_of% H₂.w, reassoc_of% H.w]
    infer_instance
  have hy₂ : RingHom.ker (algebraMap R K) = ((g₂ ≫ g ≫ s) y₂).asIdeal := by simpa using hy
  exact Near.of_pullback f H (Near.of_pullback f' H₂ (near_isIso (g₂ ≫ g ≫ s) f₂ K y₂ hy₂))

theorem isOpen_near (Q : MorphismProperty Scheme.{0}) : IsOpen {x : X | Near f Q x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨T, T', g, g', f', H, hg, hx, hQ⟩
  have := hg
  exact ⟨Set.range g, fun z hz => ⟨T, T', g, g', f', H, hg, hz, hQ⟩, g.isOpenEmbedding.isOpen_range, hx⟩

theorem isIso_of_near {S : Scheme.{0}} (t : S ⟶ X)
    (h : ∀ y : S, Near f (MorphismProperty.isomorphisms _) (t y)) : IsIso (pullback.snd f t) := by
  choose T T' g g' f' H hg hx hQ using h
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun y => t ⁻¹ᵁ (g y).opensRange) ?_ fun y => ?_
  · refine eq_top_iff.mpr fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, ?_⟩
    simpa using hx z
  · have := hg y
    have : IsIso (f' y) := hQ y
    have hle : Set.range (Scheme.Opens.ι (t ⁻¹ᵁ (g y).opensRange) ≫ t) ⊆ Set.range (g y) := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    have hu := IsOpenImmersion.lift_fac (g y) _ hle
    have big := (isPullback_morphismRestrict (pullback.snd f t) (t ⁻¹ᵁ (g y).opensRange)).paste_vert
      (IsPullback.of_hasPullback f t).flip
    rw [← hu] at big
    rw [MorphismProperty.isomorphisms.iff]
    exact (big.of_bot' (H y)).isIso_fst_of_isIso

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y X : Scheme.{0}) (s : X ⟶ Sp R) (φ : Y ⟶ X) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → IsProper φ → Flat (φ ≫ s) → IsIso (pullback.snd φ (pullback.fst s (spMap x))) → ∃ f : R, x f ≠ 0 ∧ IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R (Localization.Away f))))) := by
  intro R _ _ Y X s φ K _ x hs _ hφ hflat hiso
  let : Algebra R K := x.toAlgebra
  have : IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R K)))) := hiso
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hU : IsOpen {z : X | Near φ (MorphismProperty.isomorphisms _) z} := isOpen_near φ _
  have hZ : IsClosed (s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ) :=
    s.isClosedMap _ hU.isClosed_compl
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hp : p ∉ s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ := by
    rintro ⟨z, hz, hsz⟩
    refine hz (near_isIso_of_isProper s φ K z ?_)
    rw [hsz]
    rfl
  obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hZ.isOpen_compl
  refine ⟨f, fun h0 => (PrimeSpectrum.mem_basicOpen _ _).mp hpf (RingHom.mem_ker.mpr h0), ?_⟩
  refine isIso_of_near φ _ fun y => ?_
  by_contra hy
  have hmem : s (pullback.fst s (spMap (algebraMap R (Localization.Away f))) y) ∈
      PrimeSpectrum.basicOpen f := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    refine (PrimeSpectrum.mem_basicOpen _ _).mpr fun hf => ?_
    have hf' : algebraMap R (Localization.Away f) f ∈
        (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).asIdeal := hf
    exact (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hf' (IsLocalization.Away.algebraMap_isUnit f))
  exact hsub hmem ⟨_, hy, rfl⟩

end GlobalTheory.NearFibreIso

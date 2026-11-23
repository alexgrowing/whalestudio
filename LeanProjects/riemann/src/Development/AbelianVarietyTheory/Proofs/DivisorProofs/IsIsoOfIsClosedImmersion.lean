import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoFibreOfPullback
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbMonoIso

open GlobalTheory.NearFibreIso

theorem fibre_isIso {R : Type} [CommRing R] {X Y : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
    [IsClosedImmersion f] [GeometricallyConnected s] [Surjective (f ≫ s)] {g g' : ℕ}
    (hg' : SmoothOfRelativeDimension g' s) (hg : SmoothOfRelativeDimension g (f ≫ s))
    (hle : g' ≤ g) (K : Type) [Field K] [Algebra R K] :
    IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K)))) := by
  have H₁ := IsPullback.of_hasPullback f (pullback.fst s (spMap (algebraMap R K)))
  have H₂ := IsPullback.of_hasPullback s (spMap (algebraMap R K))
  have H := H₁.paste_vert H₂
  have h₁ : SmoothOfRelativeDimension g' (pullback.snd s (spMap (algebraMap R K))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H₂ hg'
  have h₂ : SmoothOfRelativeDimension g (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback H hg
  have : Surjective (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) := MorphismProperty.of_isPullback H ‹_›
  have : Smooth s := hg'.smooth
  have : AlgebraicGeometry.IsIntegral (Limits.pullback s (spMap (algebraMap R K))) := GlobalTheory.isIntegral_of_isPullback_of_smooth H₂
  have : Smooth (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) := h₂.smooth
  have : AlgebraicGeometry.IsReduced (Limits.pullback f (pullback.fst s (spMap (algebraMap R K)))) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K)))
  have : Nonempty ↥(Limits.pullback (C := Scheme.{0}) f (pullback.fst s (spMap (algebraMap R K)))) := by
    obtain ⟨z, -⟩ := (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))).surjective (default : PrimeSpectrum K)
    exact ⟨z⟩
  exact GlobalTheory.DivisiblePart.isIso_of_dim_le _ _ h₁ h₂ hle

end GlobalTheory.AbMonoIso

namespace GlobalTheory.AbMonoIso

open GlobalTheory.NearFibreIso

theorem isIso_of_isClosedImmersion {S X Y : Scheme.{0}} [IsLocallyNoetherian S] (p : X ⟶ S)
    (f : Y ⟶ X) [IsClosedImmersion f] [GeometricallyConnected p] [Surjective (f ≫ p)]
    [Flat (f ≫ p)] {g g' : ℕ} (hg' : SmoothOfRelativeDimension g' p)
    (hg : SmoothOfRelativeDimension g (f ≫ p)) (hle : g' ≤ g) : IsIso f := by
  have : Smooth p := hg'.smooth
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : IsLocallyNoetherian (Limits.pullback p j) := isLocallyNoetherian_of_isOpenImmersion gX
    have : Flat (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : Surjective (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have h₁ : SmoothOfRelativeDimension g' s :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback HX hg'
    have h₂ : SmoothOfRelativeDimension g (f' ≫ s) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback HYS hg
    have : IsProper f' := MorphismProperty.of_isPullback HY (inferInstanceAs (IsProper f))
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    have := fibre_isIso s f' h₁ h₂ hle (s y').asIdeal.ResidueField
    have h := near_isIso_of_isProper s f' (s y').asIdeal.ResidueField y'
      (Ideal.ker_algebraMap_residueField (s y').asIdeal)
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

theorem isIso_of_mono : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g g' : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g' B'.hom → g' ≤ g → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  intro S _ B B' _ _ hB hB' g g' hg hg' hle x _ _
  have := hB.proper
  have := hB.smooth
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : Flat (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsIso x.left :=
    isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) hle
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

end GlobalTheory.AbMonoIso

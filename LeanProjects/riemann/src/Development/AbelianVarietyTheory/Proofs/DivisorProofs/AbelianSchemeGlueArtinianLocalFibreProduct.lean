import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandGlueFlatArtinianFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfIsPullbackOfSurjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfNilpotentThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GlueAb

theorem isNilpotent_ker {P R : CommRingCat.{0}} (f : P ⟶ R) [IsLocalRing P] [IsArtinianRing P]
    [Nontrivial R] : IsNilpotent (RingHom.ker f.hom) := by
  have h : IsNilpotent (IsLocalRing.maximalIdeal P) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := P)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have := Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f.hom)) n
  rw [hn] at this
  exact le_antisymm this bot_le

theorem surjective_spec_map {P R : CommRingCat.{0}} (f : P ⟶ R) [IsLocalRing P] [IsArtinianRing P]
    [Nontrivial R] : Surjective (Spec.map f) := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  refine ⟨y, ?_⟩
  have : Subsingleton (PrimeSpectrum P) := ⟨fun a b => PrimeSpectrum.ext <| by
    have ha := IsArtinianRing.isMaximal_of_isPrime a.asIdeal
    have hb := IsArtinianRing.isMaximal_of_isPrime b.asIdeal
    rw [IsLocalRing.eq_maximalIdeal ha, IsLocalRing.eq_maximalIdeal hb]⟩
  exact Subsingleton.elim (α := PrimeSpectrum P) _ _

theorem pullback_elem {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) :
    (∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) ∧
      (Function.Surjective g₂ → Function.Surjective f₁) := by
  have h' := (Types.isPullback_iff _ _ _ _).mp (h.map (forget CommRingCat))
  refine ⟨fun x y h1 h2 => h'.2.1 x y ⟨h1, h2⟩, fun hg r => ?_⟩
  obtain ⟨s, hs⟩ := hg (g₁ r)
  obtain ⟨p, hp, -⟩ := h'.2.2 r s hs.symm
  exact ⟨p, hp⟩

end GlobalTheory.GlueAb

namespace GlobalTheory.GlueAb

theorem main_of_nontrivial (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀)
    (g₂ : R₂ ⟶ R₀) (hpb : IsPullback f₁ f₂ g₁ g₂) (hl : IsLocalRing P) (ha : IsArtinianRing P)
    (hg₁ : Function.Surjective g₁) (hg₂ : Function.Surjective g₂) (hR : Nontrivial R₁)
    (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀))
    [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left) (h₁ : IsAbelianScheme A₁)
    (h₂ : IsAbelianScheme A₂) (hψ₁ : IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁)
    (hψ₂ : IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂) :
    ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left),
      IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧
        ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := by
  haveI := h₁.smooth
  haveI := h₂.smooth
  obtain ⟨Y, j₁, j₂, hj₁, hj₂, hY, hpo⟩ := GlobalTheory.T.ferrand_glue_flat_artinian_fibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂
    A₁ A₂ A₀ ψ₁ ψ₂ hψ₁.1 hψ₂.1 inferInstance inferInstance
  obtain ⟨G, hc, hG₁, hG₂⟩ := GlobalTheory.T.exists_glued_commGroupScheme_artinFibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂ A₁ A₂ A₀ ψ₁ ψ₂
    h₁.comm h₂.comm hψ₁ hψ₂ Y j₁ j₂ hj₁ hj₂ hY hpo
  refine ⟨Y, G, j₁, j₂, ?_, hG₁, hG₂, hpo.w⟩
  have hf₁ : Function.Surjective f₁ := (pullback_elem hpb).2 hg₂
  have hN : IsNilpotent (RingHom.ker f₁.hom) := isNilpotent_ker f₁
  have hlfp : LocallyOfFinitePresentation Y.hom :=
    GlobalTheory.T.locallyOfFinitePresentation_of_nilpotent_thickening_noetherian P R₁ f₁ hf₁ hN inferInstance Y A₁ j₁ hj₁ inferInstance
  have hsm : Smooth Y.hom := GlobalTheory.smooth_of_isPullback_of_surjective_of_flat _ _ _ _ (Spec.map f₁) j₁
    A₁.hom Y.hom hj₁ (surjective_spec_map f₁) hY hlfp h₁.smooth
  obtain ⟨hp, hgc⟩ := GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift P R₁ f₁.hom hf₁ hN
    Y A₁ j₁ hj₁ hsm h₁.proper h₁.geomConnected
  exact ⟨hc, hsm, hp, hgc⟩

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂ A₁ _ A₂ _ A₀ _ ψ₁ ψ₂ h₁ h₂ hψ₁ hψ₂
  by_cases hR : Nontrivial R₁
  · exact main_of_nontrivial P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂ hR A₁ A₂ A₀ ψ₁ ψ₂ h₁ h₂ hψ₁ hψ₂
  · have hR₂ : Nontrivial R₂ := by
      by_contra hR₂
      rw [not_nontrivial_iff_subsingleton] at hR hR₂
      exact zero_ne_one ((pullback_elem hpb).1 0 1 (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    obtain ⟨A, G, φ₂, φ₁, hA, h₂', h₁', hw⟩ := main_of_nontrivial P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hpb.flip hl ha
      hg₂ hg₁ hR₂ A₂ A₁ A₀ ψ₂ ψ₁ h₂ h₁ hψ₂ hψ₁
    exact ⟨A, G, φ₁, φ₂, hA, h₁', h₂', hw.symm⟩

end GlobalTheory.GlueAb

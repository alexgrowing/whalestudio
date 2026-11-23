import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.HodgeIso

theorem main : GlobalTheory.CovTop.Hypotheses2 → ∀ {T : Scheme.{0}} (A : Over T) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ F : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV)) →
    Nonempty (F.toMod ≅ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) := by
  intro P T A _ g hA hg H e he F hF
  obtain ⟨i, hi⟩ := GlobalTheory.T.hodge_into_de_rham_injective P T A g hA hg H e he

  have haff : ∀ (W : T.Opens) (hW : IsAffineOpen W) (s : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, W)),
      i.app W s ∈ F.sec W := fun W hW s =>
    (hF W hW _).2 ((hi W hW).2.1 ▸ ⟨s, rfl⟩)
  have hmem : ∀ V s, i.app V s ∈ F.sec V := by
    intro V s
    refine F.mem_of_local fun x hx => ?_
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (X := T) (x := x) (U := V) hx
    have hWV' : W ≤ V := hWV
    refine ⟨W, hWV', hxW, ?_⟩
    rw [← GlobalTheory.Twist.app_resM]
    exact haff W hW _
  let ψ := F.lift i hmem
  have hinj : ∀ (W : T.Opens), IsAffineOpen W → Function.Injective (ψ.app W) := by
    intro W hW s s' h
    exact (hi W hW).1 (congrArg (F.incl.app W) h)
  have hsurj : ∀ (W : T.Opens), IsAffineOpen W → Function.Surjective (ψ.app W) := by
    intro W hW t
    have ht : e W hW (F.incl.app W t) ∈ PrimitiveSubmodule (onAff A hW) := (hF W hW _).1 (F.incl_app_mem t)
    rw [← (hi W hW).2.1] at ht
    obtain ⟨s, hs⟩ := ht
    refine ⟨s, F.incl_app_injective W ?_⟩
    exact (e W hW).injective hs
  have : Mono ψ := GlobalTheory.QCoh.mono_of_locally_app_injective ψ fun V x hx => by
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (X := T) (x := x) (U := V) hx
    exact ⟨W, hxW, hWV, hinj W hW⟩
  have : Epi ψ := GlobalTheory.QCoh.epi_of_locally_app_surjective ψ fun V x hx => by
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (X := T) (x := x) (U := V) hx
    exact ⟨W, hxW, hWV, hsurj W hW⟩
  have : IsIso ψ := isIso_of_mono_of_epi ψ
  exact ⟨(asIso ψ).symm⟩

end GlobalTheory.HodgeIso

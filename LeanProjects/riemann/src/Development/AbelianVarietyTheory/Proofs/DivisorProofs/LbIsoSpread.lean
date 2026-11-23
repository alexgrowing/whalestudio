import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegBundleSpread

theorem lbIso_spread : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → ∀ (j₂ : (G2 e.A).left ⟶ (G2 d₀.A).left) (φ₂ : (G2 e.A).left ⟶ (G2 u.A).left), IsPullback j e.A.hom d₀.A.hom (spMap R₀.subtype) → IsSquare j j₂ → LBIso e.P (d₀.P.pull j₂) → IsSquare (j ≫ ψ) φ₂ → LBIso e.P (u.P.pull φ₂) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left) (φ₁₂ : (G2 d₁.A).left ⟶ (G2 d₀.A).left) (χ₂ : (G2 d₁.A).left ⟶ (G2 u.A).left), IsPullback φ₁ d₁.A.hom d₀.A.hom (spMap (Subring.inclusion hle)) → IsSquare φ₁ φ₁₂ → LBIso d₁.P (d₀.P.pull φ₁₂) → IsSquare (φ₁ ≫ ψ) χ₂ → LBIso d₁.P (u.P.pull χ₂) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ j₂ φ₂ hj hj₂ hej hφ₂ heφ
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ.w
  have hcomp : j₂ ≫ ψ₂ = φ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hj₂ hψ₂ hφ₂
  have hpb : IsPullback j₂ (G2 e.A).hom (G2 d₀.A).hom (spMap R₀.subtype) :=
    GlobalTheory.SiegDesc.isPullback_of_isSquare hj hj₂
  haveI : IsProper d₀.A.hom := d₀.ab.proper
  haveI : IsProper (G2 d₀.A).hom := by
    change IsProper (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom)
    infer_instance
  have hN : (u.P.pull ψ₂).IsLB := pull_isLB u.isLB ψ₂
  have H : LBIso (d₀.P.pull j₂) ((u.P.pull ψ₂).pull j₂) := by
    have a : LBIso (d₀.P.pull j₂) (u.P.pull φ₂) :=
      LBIso.trans (pull_isLB d₀.isLB _) e.isLB (pull_isLB u.isLB _) (LBIso.symm hej) heφ
    have b : LBIso (u.P.pull φ₂) ((u.P.pull ψ₂).pull j₂) := by
      rw [← hcomp]
      exact LBIso.symm (GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ j₂)
    exact LBIso.trans (pull_isLB d₀.isLB _) (pull_isLB u.isLB _) (pull_isLB hN _) a b
  obtain ⟨F, hF⟩ := GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ (G2 e.A).left (G2 d₀.A).left
    (G2 e.A).hom (G2 d₀.A).hom j₂ d₀.P (u.P.pull ψ₂) hpb d₀.isLB hN H
  refine ⟨F, fun R₁ hle hFR s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁ hφ₁₂ hd₁ hχ₂ => ?_⟩
  have hcomp₁ : φ₁₂ ≫ ψ₂ = χ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hφ₁₂ hψ₂ hχ₂
  have H₁ := hF R₁ hle hFR (G2 d₁.A).left (G2 d₁.A).hom φ₁₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ₁ hφ₁₂)
  have c : LBIso ((u.P.pull ψ₂).pull φ₁₂) (u.P.pull χ₂) := by
    rw [← hcomp₁]
    exact GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ φ₁₂
  exact LBIso.trans d₁.isLB (pull_isLB hN _) (pull_isLB u.isLB _)
    (LBIso.trans d₁.isLB (pull_isLB d₀.isLB _) (pull_isLB hN _) hd₁ H₁) c

end GlobalTheory.SiegBundleSpread

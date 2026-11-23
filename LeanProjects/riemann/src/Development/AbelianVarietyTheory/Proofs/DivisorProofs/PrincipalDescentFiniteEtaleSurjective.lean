import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleKTrivOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLevDescent

theorem principal_of_sRel_finite_etale : ∀ (h M M₀ d d₀ : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] (ζ : B) (ζ₀ : B₀) (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : X ⟶ Sp B) (s₀ : Y ⟶ Sp B₀) (π : X ⟶ Y) (c : SiegPre h M ζ s) (c₀ : SiegPre h M₀ ζ₀ s₀), IsFinite π → Etale π → Surjective π → SRel c c₀ d d₀ π → c.Principal → c₀.Principal := by
  intro h M M₀ d d₀ B B₀ _ _ ζ ζ₀ X Y _ s s₀ π c c₀ hfin het hsurj m hc
  obtain ⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩ := m
  obtain ⟨h₁, h₂⟩ := hc
  refine ⟨(relAmple_kTriv_of_finite_etale_cover Y X π c₀.A c.A φ c₀.diag c.diag hfin het hsurj c₀.ab
    (pull_isLB c₀.isLB _) (pull_isLB c.isLB _) pb (GlobalTheory.SiegelPull.diag_iso sq iso)).1 h₁, ?_⟩
  intro T x ⟨t, ht⟩
  haveI := het
  haveI := hsurj
  let T' : Over X := Over.mk (pullback.snd T.hom π)
  let p : T'.left ⟶ T.left := pullback.fst T.hom π
  have hp : p ≫ T.hom = T'.hom ≫ π := pullback.condition
  haveI : Epi p := Flat.epi_of_flat_of_surjective _
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SiegelDescent.exists_liftHom pb T' T p hp
  have hx' : (ρ x).left ≫ φ = p ≫ x.left := (hρ x (ρ x)).1 rfl
  have w₁ : (fst c.A T').left ≫ φ ≫ c₀.A.hom = ((snd c.A T').left ≫ p) ≫ T.hom := by
    rw [pb.1.w, ← Category.assoc, Over.w (fst c.A T'), Category.assoc, hp, ← Category.assoc,
      Over.w (snd c.A T')]
  let χ : (c.A ⊗ T').left ⟶ (c₀.A ⊗ T).left := pullback.lift ((fst c.A T').left ≫ φ) ((snd c.A T').left ≫ p) w₁
  have χ₁ : χ ≫ (fst c₀.A T).left = (fst c.A T').left ≫ φ := pullback.lift_fst _ _ _
  have χ₂ : χ ≫ (snd c₀.A T).left = (snd c.A T').left ≫ p := pullback.lift_snd _ _ _
  have e : (lift (snd c.A T' ≫ ρ x) (fst c.A T')).left ≫ φ₂ = χ ≫ (lift (snd c₀.A T ≫ x) (fst c₀.A T)).left :=
    GlobalTheory.SiegelDescent.lift_square sq (τ := χ)
      (by rw [Over.comp_left, Over.comp_left, Category.assoc, hx', ← Category.assoc χ, χ₂, Category.assoc])
      χ₁.symm
  have H := GlobalTheory.SiegelDescent.lbIso_square c.isLB c₀.isLB iso e
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullPull (c₀.P.pull (lift (snd c₀.A T ≫ x) (fst c₀.A T)).left) χ) t ht
  have hg := GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB (pull_isLB c₀.isLB _) _) (pull_isLB c.isLB _)
    H.symm ⟨t₁, ht₁⟩
  have h₃ : ρ x = 1 := h₂ T' (ρ x) hg
  have h₄ : p ≫ x.left = p ≫ (1 : T ⟶ c₀.A).left := by
    rw [← hx', h₃, GlobalTheory.SiegelDescent.one_comp pb T' T p hp]
  exact Over.OverMorphism.ext ((cancel_epi p).1 h₄)

end GlobalTheory.SiegLevDescent

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AlgGroup

open GlobalTheory.LN GlobalTheory.UU GlobalTheory.AbLaw.Seesaw

theorem isPullback_of_isGrpPullback {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B']
    {f : S' ⟶ S} {F : B'.left ⟶ B.left} (h : IsGrpPullback B' B f F) : IsPullback F B'.hom B.hom f := h.1

theorem isAbelianScheme_of_thickenings_local (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) (hc : IsAdicComplete I R)
    (hc' : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)]
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hY : ∀ e, IsAbelianScheme (Y e))
    (hβ : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e))
    (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left) (hB : IsProjBy B.hom)
    (hs : Smooth B.hom) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e))
    (hβb : ∀ e, β e ≫ b (e + 1) = b e) :
    ∃ _ : GrpObj B, IsAbelianScheme B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  have hM : MorAlgSt := GlobalTheory.LN.ega_holds.2.1
  have hpr : IsProper B.hom := isProper_of_isProjBy R B.left B.hom hB
  have hs₂ : Smooth (B ⊗ B).hom := by
    change Smooth (pullback.fst B.hom B.hom ≫ B.hom)
    infer_instance
  obtain ⟨mu, hm⟩ := exists_word hM hI hc hc' hβ hB hb hβb
    (FreeGroup.of true * FreeGroup.of false) (B ⊗ B) (isProjBy_tensor R B B hB hB) hs₂
    (fun i => bif i then fst B B else snd B B)
  obtain ⟨io, hi⟩ := exists_word hM hI hc hc' hβ hB hb hβb
    (FreeGroup.of ())⁻¹ B hB hs (fun _ => 𝟙 B)
  obtain ⟨un, hu⟩ := exists_word hM hI hc hc' hβ hB hb hβb
    (1 : FreeGroup Empty) (𝟙_ _) (isProjBy_id R) (inferInstanceAs (Smooth (𝟙 _))) Empty.elim
  obtain ⟨G, hG, hG'⟩ := exists_grpObj hI (fun e => (hY e).comm) hpr hb mu io un
    (fun e T x y x₀ y₀ hx hy => by
      have := hm e T (lift x₀ y₀) (fun i => bif i then x else y) (fun i => by
        cases i
        · simpa using hy
        · simpa using hx)
      rwa [map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at this)
    (fun e T x x₀ hx => by
      have := hi e T x₀ (fun _ => x) (fun _ => by rwa [Category.comp_id])
      rwa [map_inv, FreeGroup.lift_apply_of] at this)
    (fun e T => by
      have := hu e T (toUnit _) Empty.elim (fun i => i.elim)
      rwa [map_one] at this)
  refine ⟨G, ⟨hG, hs, hpr, ?_⟩, hG'⟩
  exact geometricallyConnected_of_quotient R (I ^ (0 + 1)) (by simpa using hI) B hs hB (Y 0) (b 0) (hb 0)
    (hY 0).geomConnected

theorem exists_abelianScheme_of_tower : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsAbelianScheme (Y e)) → (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (_ : GrpObj B) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro R _ _ _ _ I hI hc hc' Y _ β hY hβ N hN hv hA
  choose v hv using hv
  obtain ⟨B, M, b, hB, hs, hM, hA', hb, hβb, hiso⟩ := GlobalTheory.LN.ega_holds.1 R I hI hc hc' Y β N v
    (fun e => isPullback_of_isGrpPullback (hβ e)) (fun e => (hY e).smooth) (fun e => ⟨hN e, hv e⟩) hA
  obtain ⟨G, hG, hG'⟩ :=
    isAbelianScheme_of_thickenings_local R I hI hc hc' Y β hY hβ B b hB hs hb hβb
  exact ⟨B, G, M, b, hG, hM, hA', hG', hβb, hiso⟩

end GlobalTheory.AlgGroup
end

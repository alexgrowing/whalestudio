import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasTrivialKernelIff
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.TwistSpanExample

theorem span_holds : TwistBCSpanStatement := twistBCSpan_of GlobalTheory.twistBaseChange

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) {k : ℕ}

theorem span_any (hk : 1 ≤ k) (α : D.X) : ∃ s : Fin (k ^ D.P.g) → D.SecB k α,
    ∀ (R' : Type) [CommRing R'] (f : R →+* R')
      (s' : LB.Sec (LB.LinComb D.P.L
        (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
        (DegPre.famε k))),
      ∃! r : Fin (k ^ D.P.g) → Γ(Spec (CommRingCat.of R'), ⊤), ∀ j, s'.f j = ∑ i,
          ((Over.mk (Spec.map (CommRingCat.ofHom f)) ⊗ D.P.A).left.presheaf.map (homOfLE le_top).op).hom
            ((fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left.appTop.hom (r i)) *
          (pullSec D.P.L (DegPre.famφB D α) (DegPre.famε k) (s i)
            (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left).f j := by
  obtain ⟨m, b, rfl, hb⟩ := GlobalTheory.twistBaseChange R D k hk α
  exact ⟨b, fun R' _ f s' => hb R' f _ (fun i j => rfl) s'⟩

theorem exists_sec_ne_zero (hk : 1 ≤ k) (α : D.X) (R' : Type) [CommRing R'] [Nontrivial R'] (f : R →+* R') :
    ∃ s' : LB.Sec (LB.LinComb D.P.L
        (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
        (DegPre.famε k)), ∃ j, s'.f j ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := span_any D hk α
  have : Nontrivial Γ(Spec (CommRingCat.of R'), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  let i₀ : Fin (k ^ D.P.g) := ⟨0, pow_pos hk _⟩
  by_contra h
  push Not at h
  have e := (hs R' f (pullSec D.P.L _ _ (s i₀) _)).unique (y₁ := fun _ => 1) (y₂ := fun _ => 0)
    (fun j => (h _ j).trans (Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (h _ j)).symm)
    (fun j => (h _ j).trans (Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (h _ j)).symm)
  exact one_ne_zero (congrFun e i₀)

theorem exists_degPre_ell (W : _root_.WeierstrassCurve R) [W.IsElliptic]
    (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ (GlobalTheory.WeierstrassCurve.ellPolAV W).A) :
    ∃ (D : DegPre R) (α : D.X) (e : D.P = GlobalTheory.WeierstrassCurve.ellPolAV W), D.P.g = 1 ∧ e ▸ D.c α = c := by
  obtain ⟨D, α, e, h⟩ := GlobalTheory.TwistCompare.exists_degPre (GlobalTheory.WeierstrassCurve.ellPolAV W) c
  exact ⟨D, α, e, by rw [e]; rfl, h⟩

end GlobalTheory.TwistSpanExample

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem exists_inv (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (D : DegData R (maximalIdeal R))
    (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
    (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U')
    (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    (∀ σ, a.act σ ≫ β = β) → ∀ σ : Gal ρ, ∃ ψ : pullback G'.hom (jK R') ⟶ pullback G'.hom (jK R'),
      ψ ≫ genMap hρ β hβ = genMap hρ β hβ ∧
      ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom ∧
      LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) ((U'.LG.L.pull (pullback.fst G'.hom (jK R'))).pull ψ) := by
  intro hinv σ
  have h₁ : G'.hom ≫ spMap (Gal.hom σ) = a.act σ ≫ G'.hom := ((a.cart σ).1.w).symm
  have h₂ : jK R' ≫ spMap (Gal.hom σ) = spMap (fracAut σ.1).toRingHom ≫ jK R' := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (fracAut_algebraMap σ.1 x).symm
  let ψ := pullback.map G'.hom (jK R') G'.hom (jK R') (a.act σ) (spMap (fracAut σ.1).toRingHom) (spMap (Gal.hom σ)) h₁ h₂
  have hψ₁ : ψ ≫ pullback.fst G'.hom (jK R') = pullback.fst G'.hom (jK R') ≫ a.act σ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom :=
    pullback.lift_snd _ _ _
  have hfr : spMap (fracAut σ.1).toRingHom ≫ spMap (fracMap ρ hρ) = spMap (fracMap ρ hρ) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact fracAut_fracMap hρ σ x
  refine ⟨ψ, ?_, hψ₂, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, genMap_fst, ← Category.assoc, hψ₁, Category.assoc, hinv σ]
    · rw [Category.assoc, genMap_snd, ← Category.assoc, hψ₂, Category.assoc, hfr]
  · obtain ⟨h, bc, hbc, hU, -⟩ := a.unif σ
    obtain ⟨wL, hwL, -⟩ := hU.lg
    have hL : LBIso U'.LG.L (U'.LG.L.pull (a.act σ)) := by
      rw [← hbc]
      exact ⟨wL, hwL⟩
    have hL₀ := U'.LG.isLB
    refine LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL₀ _) (pull_isLB (pull_isLB hL₀ _) _)
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL (pullback.fst G'.hom (jK R')) rfl) ?_
    exact GlobalTheory.GenSpread.lbIso_pull_pull hL₀ ψ hψ₁.symm

end GlobalTheory.Mum.GenDesc

import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GenMapEqOfFactor

open AlgebraicGeometry CategoryTheory MonObj
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace ModelDimension

theorem lie_lattice_local_ring : ∀ (X : Scheme.{0}) (G : CategoryTheory.Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (A : Subring Ω) [IsLocalRing A], IsCptGen ξ → AlgebraicGeometry.Smooth G.hom → ∀ (zq : Spec (CommRingCat.of A) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ zq = ξ → ∀ (hc : genPt ξ ⤳ centre zq) (e : Li), e ∈ Submodule.span A (M.lat ⟨centre zq, hc⟩ : Set Li) ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zq ⟶ G, GlobalTheory.CompanionTheory.Ar.IsTanAt G zq v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ v.left := by
  intro X G _ _ Ω _ ξ Li _ _ M A _ hξ hG zq hz hc e
  have hg := genMap_eq_of_factor (algebraMap A Ω) zq hz hc
  subst hz
  rw [← lieLat_fibAt_iff X G Ω _ Li M A zq Ω Li M hξ hG hc specializes_rfl e]
  unfold LieModel.fibAt
  refine Iff.of_eq (congrArg (fun s : Set Li => e ∈ Submodule.span A s) (Set.ext fun w => ⟨fun hw => ?_, ?_⟩))
  · obtain ⟨v, hv⟩ := ((lieLat_carrier X G Ω _ Li M _).1 w).1 hw
    refine ⟨hc, w, hw, LieFib.valAt_base M zq hc specializes_rfl v hv _
      (LieCarrier.epsHom (Scheme.stalkClosedPointTo zq).hom _ _ (Scheme.Spec_stalkClosedPointTo_fromSpecStalk zq) ≫ v)
      ?_ rfl⟩
    have e1 := LieFib.spec_dualMap_comp (Scheme.stalkClosedPointTo zq).hom (algebraMap A Ω)
    rw [← hg] at e1
    exact hv.2.trans ((congrArg (· ≫ v.left) e1).trans (Category.assoc _ _ _))
  · rintro ⟨_, e', he', h, v, hv, hw⟩
    have hg' := genMap_eq_of_factor (RingHom.id Ω) (Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ zq)
      (by rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]) h
    have h2 := hv.2
    rw [hg'] at h2
    have : w = e' := M.inj (Over.OverMorphism.ext (hw.trans h2.symm))
    rw [this]
    exact he'

end ModelDimension

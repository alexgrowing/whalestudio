import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRepOfPublished
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteTwistedKernelCubeLambdaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFiniteTwistedKernelOverAffineParameterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveTwistedKernelAdditiveLineBundleFamilyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistKernel

theorem twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧ ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  intro R _ _ A _ hA L hL ha T _ hT N hN
  have := hA.proper
  have : LocallyOfFiniteType (A ⊗ T).hom := by
    have := hT
    first
    | infer_instance
    | (show LocallyOfFiniteType (pullback.fst A.hom T.hom ≫ A.hom); infer_instance)
    | (show LocallyOfFiniteType (pullback.snd A.hom T.hom ≫ T.hom); infer_instance)
  have : IsLocallyNoetherian (A ⊗ T).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ T).hom
  have hΛ : Fam A (abelian₂ A L) := ⟨LB.isLB_linComb hL _ _,
    (GlobalTheory.CubeDual.isAdditive_lam GlobalTheory.CubeTop.cubeTheorem hA hL (LB.isLB_linComb hL _ _)).1⟩
  obtain ⟨H, h, hh, hH⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp R) A (A ⊗ T) hA
    (ev (abelian₂ A L) (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T)) (ev N (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
    (hΛ.ev (fst A T)) (hN.ev (snd A T))
  have rep : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T),
      Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
    intro Y a t
    rw [← hH Y (lift a t), same_iff hΛ.isLB hN.isLB, same_iff (hΛ.ev (fst A T)).isLB (hN.ev (snd A T)).isLB,
      evc_ev hΛ.isLB, evc_ev hN.isLB]
    simp
  exact ⟨H, h, hh, GlobalTheory.T.isFinite_twisted_kernel_cubeLambda R A hA L hL ha T hT N hN H h hh rep,
    GlobalTheory.T.flat_finiteTwistedKernel_over_affineParameter R A hA L hL ha T hT N hN H h hh rep (GlobalTheory.T.isFinite_twisted_kernel_cubeLambda R A hA L hL ha T hT N hN H h hh rep),
    GlobalTheory.T.surjective_twistedKernel_additiveLineBundleFamily R A hA L hL ha T hT N hN H h hh rep, rep⟩

end GlobalTheory.TwistKernel

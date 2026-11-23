import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseChangeUniformization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegIdentitySymmStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.UnifMove

theorem g_eq_of_isPullDeg_id {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}
    (hD : IsPullDeg (RingHom.id R) D D') : D'.P.g = D.P.g :=
  H1.dim_unique _ D'.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp hD).1 D.P.smoothDim)
    (eSec D'.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R))

theorem nonempty_isPullDeg_id_symm {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}
    (hD : IsPullDeg (RingHom.id R) D D') : Nonempty (IsPullDeg (RingHom.id R) D' D) :=
  GlobalTheory.T.isPullDeg_identity_symm R D D' hD

theorem exists_unif_of_isPullDeg_id {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    {D D' : DegData R I} (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hsa : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ U' : Unif I D' A G, U'.LG = U.LG ∧ U'.gen = U.gen := by
  have hs := specOf_id R
  let ε : G ≅ G := Iso.refl G
  haveI hε : IsMonHom ε.hom := show IsMonHom (𝟙 G) from inferInstance
  have gp₁ : IsGrpPullback G G (specOf (RingHom.id R)) ε.hom.left :=
    (isGrpPullback_of_iso ε).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have := U.gen_hom
  let eA : (Over.pullback (jK R)).obj G ≅ A.A := (Over.pullback (jK R)).mapIso ε ≪≫ U.gen
  have mE : IsMonHom eA.hom := by
    show IsMonHom ((Over.pullback (jK R)).map (𝟙 G) ≫ U.gen.hom)
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    infer_instance
  have wA : LBIso (A.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R) ≫ bc.hom.left ≫
      pullback.fst G.hom (specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := ((Over.pullback (jK R)).map ε.hom).left)
      (chartPullSame A.L (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => rfl)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => by
        rw [hbc]; exact (pullback.lift_fst _ _ _).symm) U.ext
  obtain ⟨wL, he, gL, rL⟩ := (GlobalTheory.TorsionFormCompare.rigAlong_id U.LG).read (ε := 𝟙 G) hbc hs
  obtain ⟨U', hL, hgen, -⟩ := GlobalTheory.TorsionFormCompare.exists_unif_pull_of_deg
    GlobalTheory.abelianSchemeLaws_all.1.polBaseChange GlobalTheory.abelianSchemeLaws_all.1.globalFns
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.twistBaseChange
    R R I I hR hR (RingHom.id R) (by rw [Ideal.map_id]) D A G hsa U D' hD (g_eq_of_isPullDeg_id hD) G bc mbc A rfl
    eA mE wA U.LG wL he gL rL
  refine ⟨U', hL, ?_⟩
  rw [hgen]
  ext : 1
  simp [eA, ε]

theorem unif_move : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I),
    Nonempty (IsPullDeg (RingHom.id R) D.toPre D'.toPre) → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    (∀ U' : Unif I D' A G, ∃ U : Unif I D A G, U.LG = U'.LG ∧ U.gen = U'.gen) ∧
      ∀ U : Unif I D A G, ∃ U' : Unif I D' A G, U'.LG = U.LG ∧ U'.gen = U.gen := by
  intro R _ _ I hR D D' ⟨hD⟩ A G _ _ hsa
  obtain ⟨hD'⟩ := nonempty_isPullDeg_id_symm hD
  exact ⟨fun U' => exists_unif_of_isPullDeg_id hR hD' hsa U', fun U => exists_unif_of_isPullDeg_id hR hD hsa U⟩

end GlobalTheory.Mum.UnifMove

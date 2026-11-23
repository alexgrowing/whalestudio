import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverPullbackSemiAbelianModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

namespace GlobalTheory.Poinc.Sep

theorem pullback_map_left_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) (F : G ⟶ G) :
    ((Over.pullback f).map F).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ F.left :=
  pullback.lift_fst _ _ _

theorem pullback_map_left_snd {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) (F : G ⟶ G) :
    ((Over.pullback f).map F).left ≫ pullback.snd G.hom f = pullback.snd G.hom f :=
  pullback.lift_snd _ _ _

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in

theorem exists_unif_trait : ∀ (X₁ : GlobalTheory.GSep.GSet) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (O : ZHOut X₁.ρ Y U₀ EE) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → CharZero V → ∀ (ξ : Sp V ⟶ Y.Z) (e : X₁.Ω₁ →+* FractionRing V), jK V ≫ ξ = spMap e ≫ Y.pt → (ξ ⁻¹' abLocus O.G).Nonempty → ∃ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback ξ).obj O.G)) (β : A.A.left ⟶ ((Over.pullback Y.pt).obj O.G).left), IsGrpPullback A.A ((Over.pullback Y.pt).obj O.G) (spMap e) β ∧ LBIso A.L ((O.L.L.pull (pullback.fst O.G.hom Y.pt)).pull β) ∧ ∀ F : O.G ⟶ O.G, IsMonHom F → ∃ E : EndU U.toUnifPre, E.aA.left ≫ β = β ≫ ((Over.pullback Y.pt).map F).left := by
  intro X₁ Y U₀ EE O V _ _ _ hc hch ξ e he hab
  obtain ⟨D, A, U, hl, -⟩ := O.unif V inferInstance inferInstance hc ξ hab
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  let κ : A.A.left ⟶ ((Over.pullback ξ).obj O.G).left :=
    U.gen.inv.left ≫ pullback.fst ((Over.pullback ξ).obj O.G).hom (jK V)
  have hκ : IsGrpPullback A.A ((Over.pullback ξ).obj O.G) (jK V) κ :=
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso U.gen.symm).comp
      (isGrpPullback_pullback ((Over.pullback ξ).obj O.G) (jK V))).congr (Category.id_comp _) rfl
  have hm : IsGrpPullback A.A O.G (spMap e ≫ Y.pt) (κ ≫ pullback.fst O.G.hom ξ) :=
    (hκ.comp (isGrpPullback_pullback O.G ξ)).congr he rfl
  have hp := isGrpPullback_pullback O.G Y.pt
  have w : (κ ≫ pullback.fst O.G.hom ξ) ≫ O.G.hom = (A.A.hom ≫ spMap e) ≫ Y.pt :=
    hm.1.w.trans (Category.assoc _ _ _).symm
  let β : A.A.left ⟶ pullback O.G.hom Y.pt := pullback.lift _ _ w
  have hβf : β ≫ pullback.fst O.G.hom Y.pt = κ ≫ pullback.fst O.G.hom ξ := pullback.lift_fst _ _ _
  have hβs : β ≫ pullback.snd O.G.hom Y.pt = A.A.hom ≫ spMap e := pullback.lift_snd _ _ _
  have hio : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 A.A.left := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hoi : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  refine ⟨D, A, U, β, hp.cancel (hm.congr rfl hβf.symm) hβs, ?_, fun F hF => ?_⟩
  · have h₁ : LBIso A.L (A.L.pull (𝟙 A.A.left)) :=
      (GlobalTheory.PolBaseChange.lbIso_refl A.isLB).chartPull (chartPullId A.L)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A.L _ _ rfl)
    have h₂ : LBIso (A.L.pull (𝟙 A.A.left)) (U.LG.L.pull κ) :=
      GlobalTheory.GenSpread.lbIso_pull_comp U.gen.inv.left hio.symm rfl U.ext
    have h₃ : LBIso (U.LG.L.pull κ) (O.L.L.pull (κ ≫ pullback.fst O.G.hom ξ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso hl κ rfl
    have h₄ : LBIso (O.L.L.pull (κ ≫ pullback.fst O.G.hom ξ)) ((O.L.L.pull (pullback.fst O.G.hom Y.pt)).pull β) :=
      GlobalTheory.GenSpread.lbIso_pull_pull O.L.isLB β hβf.symm
    exact LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB (pull_isLB O.L.isLB _) _) h₁
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (pull_isLB (pull_isLB O.L.isLB _) _) h₂
        (LBIso.trans (pull_isLB U.LG.isLB _) (pull_isLB O.L.isLB _) (pull_isLB (pull_isLB O.L.isLB _) _) h₃ h₄))
  · obtain ⟨E, -, hE⟩ := exists_degenerationEndomorphism_of_admissibleBase V _ ⟨inferInstance, inferInstance, inferInstance, hc⟩ D A _
      (IsSemiAbelian.pullback _ _ O.semi) U ((Over.pullback ξ).map F)
      (U.gen.inv ≫ (Over.pullback (jK V)).map ((Over.pullback ξ).map F) ≫ U.gen.hom) inferInstance inferInstance
      (by rw [Iso.hom_inv_id_assoc])
    refine ⟨E, ?_⟩
    have n₁ := pullback_map_left_fst (jK V) ((Over.pullback ξ).obj O.G) ((Over.pullback ξ).map F)
    have n₂ := pullback_map_left_fst ξ O.G F
    have n₃ := pullback_map_left_fst Y.pt O.G F
    have n₄ := pullback_map_left_snd Y.pt O.G F
    have a₁ : E.aA.left ≫ κ = κ ≫ ((Over.pullback ξ).map F).left := by
      rw [hE]
      show (U.gen.inv.left ≫ ((Over.pullback (jK V)).map ((Over.pullback ξ).map F)).left ≫ U.gen.hom.left) ≫
        U.gen.inv.left ≫ pullback.fst ((Over.pullback ξ).obj O.G).hom (jK V) =
        (U.gen.inv.left ≫ pullback.fst ((Over.pullback ξ).obj O.G).hom (jK V)) ≫ _
      rw [Category.assoc, Category.assoc, ← Category.assoc U.gen.hom.left, hoi, Category.id_comp, n₁, Category.assoc]
    apply pullback.hom_ext
    · calc (E.aA.left ≫ β) ≫ pullback.fst O.G.hom Y.pt = (E.aA.left ≫ κ) ≫ pullback.fst O.G.hom ξ := by
            exact (Category.assoc _ _ _).trans ((congrArg (E.aA.left ≫ ·) hβf).trans (Category.assoc _ _ _).symm)
        _ = (κ ≫ pullback.fst O.G.hom ξ) ≫ F.left := by
            rw [a₁]; exact (Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) n₂).trans (Category.assoc _ _ _).symm)
        _ = (β ≫ ((Over.pullback Y.pt).map F).left) ≫ pullback.fst O.G.hom Y.pt := by
            rw [← hβf]; exact (Category.assoc _ _ _).trans ((congrArg (β ≫ ·) n₃.symm).trans (Category.assoc _ _ _).symm)
    · calc (E.aA.left ≫ β) ≫ pullback.snd O.G.hom Y.pt = A.A.hom ≫ spMap e := by
            rw [Category.assoc, hβs, ← Category.assoc, Over.w]
        _ = (β ≫ ((Over.pullback Y.pt).map F).left) ≫ pullback.snd O.G.hom Y.pt := by
            exact hβs.symm.trans ((congrArg (β ≫ ·) n₄.symm).trans (Category.assoc _ _ _).symm)

end GlobalTheory.Poinc.Sep

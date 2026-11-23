import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRootStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.GenRestrict

theorem exists_genericPoints_equiv_any : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ g : R →+* V, Function.Injective g → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'), LBIso U'.LG.L (U.LG.L.pull β) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
      ∃ e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A),
        (∀ (k : ℕ) (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) ∧
        (∀ (σ : F →ₐ[FractionRing V] F) (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) ∧
        ∀ x : TFK (R := V) F ⟶ A'.A, (e x).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV hDVR g hinj G' _ _ β h hG' D' A' U' hL F _ _ _ _ hc
  obtain ⟨gR, lR⟩ := unifPre_generic U.toUnifPre
  obtain ⟨gV, lV⟩ := unifPre_generic U'.toUnifPre
  have gVG : IsGrpPullback A'.A G (jK V ≫ spMap g) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ β) :=
    gV.comp h
  have hcomp : jFK (R := V) F ≫ jK V ≫ spMap g = jFK (R := R) F ≫ jK R := by
    have e1 : (algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp g) =
        (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) := RingHom.ext fun r => (hc r).symm
    calc jFK (R := V) F ≫ jK V ≫ spMap g
        = spMap ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp g)) := by
          rw [spMap_comp_eq (algebraMap (FractionRing V) F), spMap_comp_eq (algebraMap V (FractionRing V)) g]
      _ = spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) := by rw [e1]
      _ = jFK (R := R) F ≫ jK R := spMap_comp_eq _ _
  obtain ⟨eV, heV⟩ := GlobalTheory.LiePull.exists_pushEquiv gVG (TFK (R := V) F) (jFK (R := V) F ≫ jK V ≫ spMap g) rfl
  obtain ⟨eR, heR⟩ := GlobalTheory.LiePull.exists_pushEquiv gR (TFK (R := R) F) (jFK (R := V) F ≫ jK V ≫ spMap g) hcomp
  obtain ⟨eR₀, heR₀⟩ := GlobalTheory.LiePull.exists_pushEquiv gR (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have hlast : ∀ x, (eR.symm (eV x)).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := fun x => by
    rw [← heR, MulEquiv.apply_symm_apply, heV]
    simp only [Category.assoc]
  have lVG : LBIso A'.L (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ β)) :=
    LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) lV
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull U'.LG.L _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => β) _ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) fun _ => rfl) hL)
  refine ⟨eV.trans eR.symm, fun k x y c hw => ?_, fun σ x x' hx => ?_, fun x => ?_⟩
  · have h1 := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G A'.A _ _ U.LG.L A'.L U.LG.isLB A'.isLB gVG lVG
      (TFK (R := V) F) k x y (eV x) (eV y) (unitOn c) (heV x) (heV y)).1 hw
    have h2 := (weilIs_congr_base G U.LG.L k hcomp (eV x) (eV y) (eR₀ (eR.symm (eV x))) (eR₀ (eR.symm (eV y)))
      (by rw [heR₀, ← heR, MulEquiv.apply_symm_apply]) (by rw [heR₀, ← heR, MulEquiv.apply_symm_apply]) _).1 h1
    exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G A.A _ _ U.LG.L A.L U.LG.isLB A.isLB gR lR
      (TFK (R := R) F) k _ _ _ _ (unitOn c) (heR₀ _) (heR₀ _)).2 h2
  · have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
      simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
      rw [hc r]
      exact σ.commutes _
    refine gR.1.hom_ext ?_ ?_
    · simp only [MulEquiv.trans_apply, Category.assoc, hlast, hx]
    · rw [Over.w, Category.assoc, Over.w]
      show jFK (R := R) F = spMap σ.toRingHom ≫ jFK (R := R) F
      rw [← spMap_comp_eq, hσ]
  · exact hlast x

end GlobalTheory.GenRestrict

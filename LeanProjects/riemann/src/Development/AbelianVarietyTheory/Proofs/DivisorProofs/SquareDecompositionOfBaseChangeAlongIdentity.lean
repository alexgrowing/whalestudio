import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerDecompositionFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecIdBC

theorem sqDec_of_baseChange_id : ∀ (F : Type) [CommRing F] (A : Over (Sp F)) [GrpObj A] (L M : LB A.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (RingHom.id F))).obj A) (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) → SqDec A L M := by
  intro F _ A _ L M hL hM hD
  have hid : spMap (RingHom.id F) = 𝟙 (Sp F) := by
    simp [spMap]
  have hw : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id F) := by rw [hid]; simp
  let π' : A.left ⟶ pullback A.hom (spMap (RingHom.id F)) := pullback.lift (𝟙 _) A.hom hw
  have e₁ : π' ≫ pullback.fst A.hom (spMap (RingHom.id F)) = 𝟙 _ := pullback.lift_fst _ _ _
  have e₂ : π' ≫ ((Over.pullback (spMap (RingHom.id F))).obj A).hom = A.hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact pullback.lift_snd _ _ _
  have hP : IsGrpPullback A ((Over.pullback (spMap (RingHom.id F))).obj A) (𝟙 _) π' := by
    have n : IsGrpPullback A A (𝟙 _ ≫ spMap (RingHom.id F)) (π' ≫ pullback.fst A.hom (spMap (RingHom.id F))) := by
      rw [e₁, Category.id_comp, hid]; exact GlobalTheory.SiegLower.isGrpPullback_id A
    exact IsGrpPullback.cancel (isGrpPullback_pullback A _) n e₂
  obtain ⟨N, a₀, r, e, β, hN, ha₀, hβ, hI⟩ := hD
  have hβ' : ∀ i, ∃ g : A ⟶ A, IsMonHom g ∧ g.left ≫ π' = π' ≫ (β i).left := fun i => by
    haveI := hβ i
    exact GlobalTheory.HomDescent.exists_isMonHom_pull hP hP (β i)
  choose β' hβ'm hβ'c using hβ'
  have iL : LBIso L ((L.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hL (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (GlobalTheory.SiegLower.lbIso_pull_id hL)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hL) _ _ _ π' (fun _ => by rw [e₁]; simp))
  have iM : LBIso M ((M.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hM (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (GlobalTheory.SiegLower.lbIso_pull_id hM)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hM) _ _ _ π' (fun _ => by rw [e₁]; simp))
  refine ⟨N, a₀, r, e, β', hN, ha₀, hβ'm, ?_⟩
  have j₁ : LBIso (lbPow L N) ((lbPow (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) N).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iL _ _ _ π' (fun _ => by simp)
  have j₂ := GlobalTheory.RigidBundleGlue.LBIso.pull hI π'
  have j₃ : LBIso (LB.LinComb M (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β' i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ))
      ((LB.LinComb (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ)).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iM _ _ _ π' (fun o => by
      cases o with
      | none => simp
      | some i => exact hβ'c i)
  exact LBIso.trans (isLB_lbPow hL N) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₁
    (LBIso.trans (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
      (pull_isLB (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hM _) _ _) _)
      (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₂ (LBIso.symm j₃))

end GlobalTheory.SqDecIdBC

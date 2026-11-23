import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyPotentialSemiAbelianModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.PolSemiAbModel

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem exists_model : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (P : PolAV (Sp (FractionRing W))),
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : W →+* V₁)
      (fK : FractionRing W →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap W _ a) = algebraMap V₁ _ (f a)) ∧
      ∃ (A : PolAV (Sp (FractionRing V₁))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧
        LBIso A.L (P.L.pull β) ∧
        ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
          IsSemiAbelian G ∧ IsMonHom gen.hom := by
  intro W _ _ _ hW P
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  haveI : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  obtain ⟨W', L, _, _, _, _, _, _, _, _, hsq, hfin, hloc, hcompl, G, _, ⟨e, he⟩, hG⟩ :=
    GlobalTheory.SS.potModel_isSemiAbelian W (FractionRing W) P.A P.isAb
  have hinj : Function.Injective (algebraMap W W') := by
    have h2 : Function.Injective ((algebraMap (FractionRing W) L).comp (algebraMap W (FractionRing W))) :=
      (algebraMap (FractionRing W) L).injective.comp (IsFractionRing.injective W (FractionRing W))
    rw [← hsq] at h2
    exact Function.Injective.of_comp h2
  haveI : CharZero W' := charZero_of_injective_algebraMap hinj
  let ε : FractionRing W' ≃ₐ[W'] L := IsLocalization.algEquiv (nonZeroDivisors W') (FractionRing W') L
  let fK : FractionRing W →+* FractionRing W' := (ε.symm : L →+* FractionRing W').comp (algebraMap (FractionRing W) L)
  have hε : (ε.symm : L →+* FractionRing W').comp (algebraMap W' L) = algebraMap W' (FractionRing W') := by
    ext x; exact ε.symm.commutes x
  obtain ⟨A, β, hpb, -, hLB⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P fK
  haveI : IsCommMonObj G := hG.comm
  refine ⟨W', inferInstance, inferInstance, inferInstance, algebraMap W W', fK,
    (GlobalTheory.LN.cDvr_iff W').2 ⟨inferInstance, hcompl, inferInstance⟩, hinj, hloc,
    RingHom.finite_algebraMap.2 hfin, ?_, A, β, hpb, hLB, ?_⟩
  · intro a
    show ε.symm (algebraMap (FractionRing W) L (algebraMap W _ a)) = _
    rw [← RingHom.comp_apply, ← hsq, RingHom.comp_apply]
    exact ε.symm.commutes _
  · let X := (Over.pullback (spMap (algebraMap W' L))).obj G
    let T := (Over.pullback (spMap (ε.symm : L →+* FractionRing W'))).obj X
    have h₁ := isGrpPullback_pullback G (jK W')
    have hTX := isGrpPullback_pullback X (spMap (ε.symm : L →+* FractionRing W'))
    have hXG := isGrpPullback_pullback G (spMap (algebraMap W' L))
    have hTG := (hTX.comp hXG).congr (by rw [spMap_comp', hε]) rfl
    obtain ⟨e₁, he₁, -⟩ := grpPullback_iso h₁ hTG
    have hXY := isGrpPullback_of_iso e
    have hYP := isGrpPullback_pullback P.A (spMap (algebraMap (FractionRing W) L))
    have hTP := (hTX.comp (hXY.comp hYP)).congr (by rw [Category.id_comp, spMap_comp']) rfl
    obtain ⟨e₂, he₂, -⟩ := grpPullback_iso hTP hpb
    exact ⟨G, inferInstance, inferInstance, e₁ ≪≫ e₂, hG, by simp only [Iso.trans_hom]; infer_instance⟩

end GlobalTheory.PolSemiAbModel

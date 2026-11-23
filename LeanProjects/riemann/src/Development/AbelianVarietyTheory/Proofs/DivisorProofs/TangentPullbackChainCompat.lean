import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TangentBaseChange

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_tangent_baseChange : ∀ (R₀ R : Subring ℂ) (ic : R₀ →+* R), (∀ x, ((ic x : R) : ℂ) = x) →
  ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A]
    (g : G.left ⟶ G₀.left) (p : A.left ⟶ G.left), IsGrpPullback G G₀ (spMap ic) g → IsGrpPullback A G (spMap R.subtype) p →
    ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : epsR ℂ ⟶ A), IsTangent v₀ →
      v'.left ≫ p ≫ g = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left →
      ∃ v : epsR R ⟶ G, IsTangent v ∧ v'.left ≫ p = spMap (Chart.dualMapR R.subtype) ≫ v.left := by
  intro R₀ R ic hic G₀ _ G _ A _ g p hg hp v₀ v' hv₀ hv'
  have hw : (spMap (Chart.dualMapR ic) ≫ v₀.left) ≫ G₀.hom =
      spMap (algebraMap R (DualNumber R)) ≫ spMap ic := by
    rw [Category.assoc, Over.w v₀]
    show spMap (Chart.dualMapR ic) ≫ spMap (algebraMap R₀ (DualNumber R₀)) = _
    rw [spMap_comp_ring, spMap_comp_ring]
    congr 1
    ext x
    · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let vl : (epsR R).left ⟶ G.left := hg.1.lift _ _ hw
  have hvg : vl ≫ g = spMap (Chart.dualMapR ic) ≫ v₀.left := hg.1.lift_fst _ _ hw
  have hvG : vl ≫ G.hom = spMap (algebraMap R (DualNumber R)) := hg.1.lift_snd _ _ hw
  refine ⟨Over.homMk vl hvG, ?_, ?_⟩
  · show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ vl = η[G].left
    apply hg.1.hom_ext
    · have e : η[G].left ≫ g = spMap ic ≫ η[G₀].left := GlobalTheory.PolBaseChange.eSec_comm hg
      have t : spMap (TrivSqZeroExt.fstHom R₀ R₀ R₀).toRingHom ≫ v₀.left = η[G₀].left := hv₀
      have hr : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (Chart.dualMapR ic) =
          ic.comp (TrivSqZeroExt.fstHom R₀ R₀ R₀).toRingHom := by
        refine RingHom.ext fun x => ?_
        simp [Chart.dualMapR]
      rw [Category.assoc, hvg, ← Category.assoc, spMap_comp_ring, hr, ← spMap_comp_ring,
        Category.assoc, t, e]
    · have hr : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (algebraMap R (DualNumber R)) =
          RingHom.id R := by
        refine RingHom.ext fun x => ?_
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [Category.assoc, hvG, spMap_comp_ring, hr, Over.w η[G]]
      simp
  · apply hg.1.hom_ext
    · have hr : (Chart.dualMapR R.subtype).comp (Chart.dualMapR ic) = Chart.dualMapR R₀.subtype := by
        refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
        · simp [Chart.dualMapR, hic]
        · simp [Chart.dualMapR, hic]
      show (v'.left ≫ p) ≫ g = (spMap (Chart.dualMapR R.subtype) ≫ vl) ≫ g
      rw [Category.assoc, hv', Category.assoc, hvg, ← Category.assoc, spMap_comp_ring, hr]
    · show (v'.left ≫ p) ≫ G.hom = (spMap (Chart.dualMapR R.subtype) ≫ vl) ≫ G.hom
      rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w v', Category.assoc, hvG]
      show spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap R.subtype =
        spMap (Chart.dualMapR R.subtype) ≫ spMap (algebraMap R (DualNumber R))
      rw [spMap_comp_ring, spMap_comp_ring]
      congr 1
      ext x
      · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.TangentBaseChange

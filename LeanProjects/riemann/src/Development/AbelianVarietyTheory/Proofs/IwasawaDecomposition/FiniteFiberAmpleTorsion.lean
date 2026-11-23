import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocallyQuasiFiniteOfTrivialOnFibres
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.FibreFinite

theorem finite_preimage : ∀ {S S' T : Scheme.{0}} (q : S ⟶ T) (h : S ⟶ S') (L : LB S'), IsProper q → IsAffineHom h →
    ∀ hA : GlobalTheory.IsAmpleLB L, ∀ t : T,
    (∃ m : ℕ, 0 < m ∧ GlobalTheory.CechPic.pull (q.fiberι t ≫ h) (m • GlobalTheory.CechPic.cls L hA.isLB) = 0) → (q ⁻¹' {t}).Finite := by
  intro S S' T q h L hq hh hA t ⟨m, hm, hc⟩
  let F := q.fiber t
  let ι : F ⟶ S := q.fiberι t
  let a : F ⟶ Sp (T.residueField t) := q.fiberToSpecResidueField t
  have hpb : IsPullback ι a q (T.fromSpecResidueField t) := IsPullback.of_hasPullback _ _
  have hy := GlobalTheory.AmpleFibre.isAffineHom_of_field (T.fromSpecResidueField t)
  have : IsAffineHom ι := MorphismProperty.of_isPullback hpb.flip hy
  have : IsProper a := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom (ι ≫ h) := inferInstance
  have hA' := hA.pull_of_isAffineHom (ι ≫ h)
  have hL' : (L.pull (ι ≫ h)).IsLB := hA'.isLB
  have hP : (lbPow (L.pull (ι ≫ h)) m).IsLB := isLB_lbPow hL' m
  have h0 : CechPic.cls _ hP = 0 := by
    rw [CechPic.cls_lbPow hL' m hP, CechPic.cls_pull hA.isLB _ hL', ← map_nsmul]
    exact hc
  obtain ⟨g, hg⟩ := (CechPic.cls_eq_zero_iff hP).1 h0
  have hI : LBIso (LB.triv F) (lbPow (L.pull (ι ≫ h)) m) := (CechPic.iso_triv_iff _).2 ⟨g, hg⟩
  have hAm := (isAmpleLB_pow_iff hL' hm).2 hA'
  have hT : IsAmpleLB (LB.triv F) := hAm.of_lbIso (LB.isLB_triv F) hI
  have : F.IsQuasiAffine := isAmpleLB_triv_iff.1 hT
  have : IsAffine F := GlobalTheory.AmpleStabFinite.isAffine_of_quasiAffine a
  have : IsFinite a := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set F).Finite := by
    have := a.finite_preimage_singleton (IsLocalRing.closedPoint (T.residueField t))
    exact this.subset fun x _ => Subsingleton.elim _ _
  rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
  exact hfin.image _

end GlobalTheory.FibreFinite

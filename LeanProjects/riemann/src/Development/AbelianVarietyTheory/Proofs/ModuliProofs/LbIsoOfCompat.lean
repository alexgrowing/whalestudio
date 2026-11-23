import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawRigidifiedLineBundleDenseFibresStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompatOfLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

theorem lbIso_of_compat : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [IsReduced R] (s : Sp R ⟶ Sp o) (t t' : TObj g k J b s) (Sg : Set (Sp R)) (φ : t.A.left ⟶ t'.A.left), Dense Sg → GeoGood t t' Sg → Compat t t' (𝟙 _) φ → IsGrpPullback t.A t'.A (𝟙 _) φ → LBIso t.L (t'.L.pull φ) := by
  intro o _ g k J b R _ _ s t t' Sg φ hd hg hc hφ
  have hp := pull_isLB t'.isLB φ
  have hN := LB.isLB_div hp t.isLB
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ t.A.left),
      CechPic.pull (f ≫ φ) (CechPic.cls _ t'.isLB) = CechPic.pull f (CechPic.cls _ t.isLB) →
      ∃ w : ((LB.div (t'.L.pull φ) t.L).pull f).Gen, w.IsGen := fun f e => by
    refine (CechPic.cls_eq_zero_iff (pull_isLB hN f)).1 ?_
    rw [CechPic.cls_pull hN, CechPic.cls_div hp t.isLB, map_sub, CechPic.cls_pull t'.isLB, ← CechPic.pull_comp, e, sub_self]
  refine GlobalTheory.T.seesaw_rigidified_lineBundle_dense_fibres R t.A t.L _ Sg t.ab t.isLB t.ample hN hd (key _ ?_) fun p hpS => ?_
  · have e : eSec t.A ≫ φ = eSec t'.A := (PolBaseChange.eSec_comm hφ).trans (Category.id_comp _)
    have e₁ := (CechPic.cls_eq_zero_iff (pull_isLB t.isLB _)).2 t.rigid
    have e₂ := (CechPic.cls_eq_zero_iff (pull_isLB t'.isLB _)).2 t'.rigid
    rw [e]
    exact e₂.trans e₁.symm
  · obtain ⟨Ω, _, _, i, su, u, ψ, ψ', h₁, h₂⟩ := hg ((Sp R).residueField p) ((Sp R).fromSpecResidueField p) (by
      rw [Scheme.range_fromSpecResidueField]; exact Set.singleton_subset_iff.2 hpS)
    refine ⟨Ω, inferInstance, _, _, ψ, _, ⟨(default : PrimeSpectrum Ω), ?_⟩, h₁.1.1, key ψ ?_⟩
    · exact Scheme.fromSpecResidueField_apply p _
    · rw [hc.fibre h₁ h₂]
      exact ((CechPic.cls_eq_iff u.isLB (pull_isLB t'.isLB _)).2 h₂.2.1).symm.trans
        ((CechPic.cls_eq_iff u.isLB (pull_isLB t.isLB _)).2 h₁.2.1)

end GlobalTheory.TUniq

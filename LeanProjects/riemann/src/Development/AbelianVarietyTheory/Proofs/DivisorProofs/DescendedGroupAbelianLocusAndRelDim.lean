import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.DescAb

theorem abLocus_eq (X S : Scheme.{0}) (j : X ⟶ S) (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (hc : ∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁)
      (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧
        ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) :
    abLocus G = Set.range j := by
  ext x
  obtain ⟨R, _, _, ξ, G₁, _, π, hx, hp, hab⟩ := hc x
  have h := abLocus_pullback abLocusOne hG hp.1 (closedPoint R)
  rw [hx] at h
  have h' := hab (closedPoint R)
  rw [hx] at h'
  exact h.trans h'

theorem relDim (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j] (hj : IsDominant j) (A : Over X) [GrpObj A]
    (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ) (hA : SmoothOfRelativeDimension g A.hom)
    (hG : IsSemiAbelian G) (hpb : IsGrpPullback A G j e) : SmoothOfRelativeDimension g G.hom := by
  have : Smooth G.hom := hG.smooth
  have hopen : IsOpenMap G.hom := G.hom.isOpenMap
  choose n W hW hd using H1.exists_dim G.hom
  have key : ∀ y, n y = g := by
    intro y
    obtain ⟨x, w, hwW, hx⟩ := j.denseRange.exists_mem_open (hopen _ (W y).isOpen) ⟨_, ⟨y, hW y, rfl⟩⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback w x hx
    refine H1.dim_base hpb.1 (hd y) hA (hpb.1.isoPullback.inv z) ?_
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
    exact hwW
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  rw [← key y]; exact hd y

end GlobalTheory.DescAb

theorem GlobalTheory.DescAb.abLocus_eq_range_and_relDim : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsSemiAbelian G → IsGrpPullback A G j e → (∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁) (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧ ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) → abLocus G = Set.range j ∧ SmoothOfRelativeDimension g G.hom := by
  intro X S j _ hj A _ G _ e g _ hA hG hpb hc
  exact ⟨GlobalTheory.DescAb.abLocus_eq X S j G hG hc, GlobalTheory.DescAb.relDim X S j hj A G e g hA hG hpb⟩

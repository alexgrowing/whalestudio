import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldExtensionEtaleCover
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemoval
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem notMem_support_comap_top {A C : Scheme.{u}} (h : A ⟶ C) (x : ↥A) :
    x ∉ ((⊤ : C.IdealSheafData).comap h).support := by
  rw [Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.support_top]
  intro hx
  have hx' : x ∈ ((⊥ : TopologicalSpace.Closeds ↥A) : Set ↥A) := hx
  simp at hx'

theorem center_ne_top_of_isPullbackSequenceOfBlowups_id {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (h : IsPullbackBlowupSequence (𝟙 X) s s) :
    ∀ i : ℕ, i < s.length → s.center i ≠ ⊤ := by
  obtain ⟨r, _e, _hlt, hmono, htop, hsupp, -⟩ := h
  have hgeid : ∀ i : ℕ, i ≤ s.length → i ≤ r i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have h1 : r n < r (n + 1) := hmono n (n + 1) hn (Nat.lt_succ_self n)
      have h2 : n ≤ r n := ih (Nat.le_of_succ_le hn)
      omega
  have hleid : ∀ d i : ℕ, i + d = s.length → r i + d ≤ s.length := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hii : i = s.length := by omega
      subst hii
      rw [htop]
      omega
    | succ m ih =>
      intro i hi
      have hi1 : (i + 1) + m = s.length := by omega
      have h2 := ih (i + 1) hi1
      have h3 : r i < r (i + 1) := hmono i (i + 1) (by omega) (Nat.lt_succ_self i)
      omega
  have hrid : ∀ i : ℕ, i ≤ s.length → r i = i := by
    intro i hi
    have h1 := hgeid i hi
    have h2 := hleid (s.length - i) i (by omega)
    omega
  intro i hi hc
  obtain ⟨x, hx⟩ := (hsupp i hi).mpr ⟨i, hi, hrid i hi.le⟩
  rw [hc] at hx
  exact notMem_support_comap_top _ x hx

theorem AffineResolutionRule.center_ne_top (B : AffineResolutionRule.{u}) (hB : IsCompatibleWithOpenImmersions B)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] :
    ∀ i : ℕ, i < (B k Y p).length → (B k Y p).center i ≠ ⊤ :=
  center_ne_top_of_isPullbackSequenceOfBlowups_id (B k Y p) (hB k Y Y p p (𝟙 Y) (Category.id_comp p))

theorem inducedRuleCompatibleWithFieldExtension (B : AffineResolutionRule.{u}) : InducedRuleCompatibleWithFieldExtension B := by
  intro hoi hfe F hF k _ _ X f _ _ _ K _ _ _ _
  obtain ⟨W, c, g, hWaff, hWred, hqlft, hqqc, hcet, hcsur, hYaff, hYred, hglft, hgqc, hget,
    hgsur, hgstruct, hgproj⟩ := exists_etale_surjective_affine_cover_baseChange X f K
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hcet
  have := hcsur
  have := hYaff
  have := hYred
  have := hglft
  have := hgqc
  have := hget
  have := hgsur
  have h0 : IsStrictPullbackBlowupSeq (baseChangeProjection f K)
      ((F k X f).baseChange (baseChangeProjection f K)) (F k X f) :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hw : IsStrictPullbackBlowupSeq g
      (((F k X f).baseChange (baseChangeProjection f K)).baseChange g)
      ((F k X f).baseChange (baseChangeProjection f K)) :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hcomp := hw.comp h0
  rw [hgproj] at hcomp
  have htW : IsStrictPullbackBlowupSeq c (B k W (c ≫ f)) (F k X f) :=
    hF k X f W (c ≫ f) c rfl AlgebraicGeometry.Surjective.surj
  have htK : IsStrictPullbackBlowupSeq (baseChangeProjection (c ≫ f) K)
      (B K (baseChange (c ≫ f) K) (baseChangeToSpec (c ≫ f) K)) (B k W (c ≫ f)) :=
    hfe k W (c ≫ f) K
  have hEqw := hcomp.isomorphic (htK.comp htW)
  have hntop := AffineResolutionRule.center_ne_top B hoi K (baseChange (c ≫ f) K)
      (baseChangeToSpec (c ≫ f) K)
  have hEq := (SequenceOfBlowups.Isomorphic.withoutIsoBlowups hEqw).trans (SequenceOfBlowups.withoutIsoBlowups_isomorphic_self _ hntop)
  have h₂ : IsStrictPullbackBlowupSeq g (B K (baseChange (c ≫ f) K) (baseChangeToSpec (c ≫ f) K))
      (F K (baseChange f K) (baseChangeToSpec f K)) :=
    hF K (baseChange f K) (baseChangeToSpec f K) (baseChange (c ≫ f) K)
      (baseChangeToSpec (c ≫ f) K) g hgstruct AlgebraicGeometry.Surjective.surj
  have hdesc := IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hw.withoutIsoBlowups h₂ hEq
  exact h0.isPullbackSequenceOfBlowups_withoutIsoBlowups.of_isomorphic hdesc

end FunctorialResolution.EmbeddedResolution

end

import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OnWithOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundParameterRequirementsEventuallyFamilyStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RowsOfPageFix
import Formalism.LocalRingCardinality.NFLeTwoMulTSq

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.OntoNum

theorem pageNum_along : ∀ x₁ : ℝ, Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    PageNum (Fm.parT x hx ι) x₁ ∧ 3 ≤ (Fm.L x ι).sc.x ∧ ((Fm.D x ι).R.k : ℝ) * (Fm.L x ι).sc.b' ≤ (Fm.L x ι).sc.b ∧
      3 ≤ (Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 5) ∧ 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (Fm.D x ι).R.nV := by
  intro x₁
  obtain ⟨ε1, hε1, hS⟩ := GlobalTheory.T.indexBoundParameterRequirements_eventually_family
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := hS eps he hle
  refine ⟨K.sup ⟨1000, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL
  have hCP : (1000 : ℝ) ≤ Fm.CP := hL2.1 Fm.CP (by simp [FamP.cPre])
  obtain ⟨xa, hxa⟩ := hK Fm CH hc hL1
  obtain ⟨xb, hxb⟩ := GlobalTheory.FinalRows.rows_of_pageFix eps Fm hc.1 hCP
  refine ⟨max (max xa xb) x₁, fun x hx hx0 ι => ?_⟩
  have hs := hxa x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0) ι
  obtain ⟨hSz, hCnW, hg, hCP', hz, -, -, hsx, -⟩ := hxb x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0) ι
  have hx1 : x₁ ≤ (Fm.L x ι).sc.x := by rw [hsx]; exact le_trans (le_max_right _ _) hx0
  exact ⟨⟨hSz, hCnW, hg, hCP', hz, hx1⟩, GlobalTheory.IndexAssembly.three_le_scale_of_pow_bound hs.2.1, hs.2.2.2.2.2.2.2.2.1, by linarith [hs.2.1],
    (Fm.parT x hx ι).nV_ge⟩

end GlobalTheory.OntoNum

end

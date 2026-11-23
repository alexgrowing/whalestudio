import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RootDiagAmple

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem relAmple_pull_of_isFinite {A G : Over S} [IsProper A.hom] (χ : A ⟶ G) [IsFinite χ.left]
    {D : LB G.left} (hD : D.IsLB) (h : Out.RelAmple G D) : Out.RelAmple A (D.pull χ.left) := by
  refine relAmple_of_isAmpleLB A (pull_isLB hD _) fun V hV => ?_
  have le : A.hom ⁻¹ᵁ V ≤ χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have le' : χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) ≤ A.hom ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have e : A.hom ⁻¹ᵁ V = χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := le_antisymm le le'
  rw [e]
  have h₁ := (isAmpleLB_of_relAmple G hD h V hV).pull_of_isFinite (χ.left ∣_ (G.hom ⁻¹ᵁ V))
  refine (isAmpleLB_congr (pull_isLB (pull_isLB hD _) _) (pull_isLB (pull_isLB hD _) _) ?_).1 h₁
  refine (cls_eq_iff (pull_isLB (pull_isLB hD _) _) (pull_isLB (pull_isLB hD _) _)).1 ?_
  rw [cls_pull (pull_isLB hD _), cls_pull (pull_isLB hD _), cls_pull hD, cls_pull hD, ← pull_comp, ← pull_comp,
    morphismRestrict_ι]

theorem relAmple_of_relAmple_pow {A : Over S} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) (h : Out.RelAmple A M) : Out.RelAmple A L := by
  rw [relAmple_iff_isAmpleLB A hM] at h
  refine relAmple_of_isAmpleLB A hL fun U hU => (isAmpleLB_pow_iff (pull_isLB hL _) hd).1 ?_
  refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)
    ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).2 (h U hU)
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

end GlobalTheory.RootDiagAmple

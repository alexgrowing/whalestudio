import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UnifTorsK.psiNormAt_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (r : ℝ), GlobalTheory.UnifTorsK.PsiNormAt p D (hD.xe χ) r ↔ GlobalTheory.UnifTorsK.PsiNormAt p D' χ r := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ r
  have key := GlobalTheory.T.norm_psi_pull_localRingsOfIntegers p V V' φ hφ hn D D' hD χ
  refine ⟨fun H j' hj' => ?_, fun H j hj => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart D.P.isLB ((D.c (hD.xe χ)).left (IsLocalRing.closedPoint V))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V) ((D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U i)).1 hi).ge
    exact (key i (j' PUnit.unit) hi' hj').trans (H (fun _ => i) hi')
  · obtain ⟨i, hi⟩ := exists_chart D'.P.isLB ((D'.c χ).left (IsLocalRing.closedPoint V'))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V') ((D'.c χ).left ⁻¹ᵁ D'.P.L.U i)).1 hi).ge
    exact (key (j PUnit.unit) i hj hi').symm.trans (H (fun _ => i) hi')

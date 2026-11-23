import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModifRefl

theorem exists_sec_canon_tens_pull_id : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D (𝟙 Y ≫ p)] (B : LB Y), B.IsLB → ∀ (s : H0 p (tens (CanonLB.all p D).bundle B) ⊤) (y : Y), y ∈ nonzeroLocus (toSec s) → ∃ s' : H0 (𝟙 Y ≫ p) (tens (CanonLB.all (𝟙 Y ≫ p) D).bundle (B.pull (𝟙 Y))) ⊤, y ∈ nonzeroLocus (toSec s') := by
  intro k _ Y p D _ inst2 B hB s y hy
  revert inst2
  generalize hq : 𝟙 Y ≫ p = q
  simp only [Category.id_comp] at hq
  subst hq
  intro inst2
  have hK : (CanonLB.all p D).bundle.IsLB := (CanonLB.all p D).isLB
  have hBp : (B.pull (𝟙 Y)).IsLB := LB.isLB_linComb hB _ _
  have H1 : LBIso (tens (B.pull (𝟙 Y)) (CanonLB.all p D).bundle) (tens B (CanonLB.all p D).bundle) :=
    GlobalTheory.CechPic.tens_congr_left hK (DescendedPrincipal.lbIso_pull_id hB)
  have H : LBIso (tens (CanonLB.all p D).bundle (B.pull (𝟙 Y))) (tens (CanonLB.all p D).bundle B) :=
    LBIso.trans (isLB_tens hK hBp) (isLB_tens hBp hK) (isLB_tens hK hB)
      (GlobalTheory.CechPic.tens_comm_iso hK hBp)
      (LBIso.trans (isLB_tens hBp hK) (isLB_tens hB hK) (isLB_tens hK hB) H1
        (GlobalTheory.CechPic.tens_comm_iso hB hK))
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_tens hK hBp) (isLB_tens hK hB) H (toSec s)
  refine ⟨H0.ofSec p ⊤ t, ?_⟩
  have e : toSec (H0.ofSec p ⊤ t) = t := by
    unfold toSec
    exact Equiv.ofBijective_symm_apply_apply _ _ _
  rw [e, ht]
  exact hy

end GlobalTheory.ModifRefl

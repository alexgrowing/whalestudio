import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralEqSumEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubschemeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem logSec_restr_secPull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} (N : HermLB p) (t : N.B.Sec)
    (i : Y ⟶ X) (σ : k →+* ℂ) :
    (MLine.ofHerm (N.restr i) σ).logSec (Cartier.secPull t i) =
      fun y => (MLine.ofHerm N σ).logSec t (ptMap i rfl σ y) :=
  funext fun y => congrArg (fun a => Real.log a / 2) ((N.φ σ).nsq_pull_secPull i rfl t y)

theorem resArch_eq_finsum_cycInt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → HermLB p) (N : HermLB p) (t : N.B.Sec) (z : X), Order.coheight z = 1 → z ∈ nonzeroLocus t → MixHt.resArch L N t z = ∑ᶠ σ : k →+* ℂ, cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t) z := by
  intro hP k _ X _ _ p e hX L N t z hz htz
  have hamb : IsAmb p := isAmb_of_isArithVar hX
  have hgen : genericPoint (clo z) ∈ nonzeroLocus (Cartier.secPull t (cloι z)) := by
    rw [Cartier.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]; exact htz
  have hd : topologicalKrullDim (clo z) = (e + 1 : ℕ) :=
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k X p hamb (e + 1) hX.dim_eq).2 z (genericPoint (clo z)) hz).1
  have hamb' : IsAmb (cloι z ≫ p) := hamb.sub (cloι z)
  have hc (σ : k →+* ℂ) := (GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme k X (clo z) p (cloι z ≫ p) σ hX.isProjOver (cloι z) rfl e
    (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t)).2
  simp only [cloι_genericPoint] at hc
  refine (dif_pos hgen).trans ?_
  rcases isArithVar_or_isEmpty hamb' hd with hv | hE
  · refine (GlobalTheory.T.mixedArchLogNormIntegral_eq_sum_embeddings hP k (clo z) (cloι z ≫ p) e hv (fun a => (L a).restr (cloι z)) (N.restr (cloι z))
      (Cartier.secPull t (cloι z)) hgen).trans (finsum_congr fun σ => ?_)
    rw [hc σ, logSec_restr_secPull]
    rfl
  · refine (mixArch_eq_zero_of_isEmpty hE _ _ _).trans (finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm
    rw [hc σ]
    haveI := hE σ
    simp only [Mix.int, MeasureTheory.integral_of_isEmpty, sub_zero]

end GlobalTheory.MixHt

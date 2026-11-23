import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NadelApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

theorem topologicalKrullDim_eq_of_smooth (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp ℂ) (D : ℕ)
    [SmoothOfRelativeDimension D q] : topologicalKrullDim X = D := by
  have hc (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
      topologicalKrullDim (U : Set X) = D := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))).trans
      (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance U hU hne)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (genericPoint X))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

theorem nadel_canonical_add : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → letI := algebraΓOfHom q; ∀ (K : CanonLB q D) (B M₀ : LB X) (hB : B.IsLB) (D₀ : CartierDiv X) (m' r : ℕ), 0 < m' → 0 < r → D₀.Eff → IsNef ℂ M₀ → IsBig ℂ M₀ → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![B] : ℚ) = interNumRed ℂ C ![toLB D₀] / m' + interNumRed ℂ C ![M₀] / r) → ∃ J : X.IdealSheafData, (∀ y : X, y ∈ J.support ↔ ¬ KltAt q D (qWeil D₀ m') y) ∧ ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) (tens K.bundle B)) i) := by
  intro hN X _ _ q D _ hproj K B M₀ hB D₀ m' r hm hr hD₀ hnef hbig hcurve
  letI := algebraΓOfHom q
  haveI := SmoothOfRelativeDimension.smooth D q
  haveI : IsNormalScheme X := isNormalScheme_of_smooth q
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  have hdim := topologicalKrullDim_eq_of_smooth X q D
  have hK := K.isLB
  have hKB := isLB_tens hK hB
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB q).1 hproj
  have hcan : toPic (canonical q D) = cls _ hK :=
    (presents_canonical q D).toPic_eq.trans ((cls_eq_iff _ _).2 (CanonLB.lbIso _ K))
  obtain ⟨J, hJ, hv⟩ := hN X q D hproj hdim (tens K.bundle B) (qWeil D₀ m') m'
    (m' • canonical q D + D₀) r M₀ hKB (isEffQDiv_qWeil hD₀ m') hm
    (isLogCanonicalMultiple_canonical hdim D₀ hm) hr hnef hbig (fun C hC => by
      have e1 := hC.interNumRed_of_cls_eq_add hH hKB hK hB (cls_tens hK hB hKB)
      have e2 := hC.interNumRed_of_cls_eq_add hH (isLB_toLB (m' • canonical q D + D₀))
        (isLB_lbPow hK m') (isLB_toLB D₀) (by
          rw [← toPic_apply, ← toPic_apply, map_add, map_nsmul, hcan, cls_lbPow hK])
      rw [e1, e2, hC.interNumRed_lbPow hH hK m']
      have : (m' : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      rw [hcurve C hC]
      field_simp
      ring)
  exact ⟨J, hJ, hv⟩

end GlobalTheory.NadelApp

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroShortGeneratorSectionImageModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortGeneratorSectionsSmallShiftedFubiniStudyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelMetricsSemiPositiveStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem horizontal_of_small : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), GlobalTheory.IsArithVar p D → ∀ (L : GlobalTheory.HermLB p), (∀ x : X, ∃ u ∈ L.smallSec, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) → ∀ (Z : AlgebraicGeometry.Scheme.{0}) (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsIntegral Z] [AlgebraicGeometry.IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) → topologicalKrullDim Z = 1 → ∃ (r : (L.restr i).B.ι → Z.functionFieldˣ) (hr : GlobalTheory.Cartier.IsRatSec (L.restr i).B r), 0 ≤ (L.restr i).curveDeg hr := by
  intro k _ X p D hX L hL Z i _ _ _ hc hd
  have hZ : GlobalTheory.IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
  obtain ⟨u, hu1, hu⟩ := hL (i (genericPoint Z))
  have hu' : genericPoint Z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull u i) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact hu
  have h0 : ∀ σ (y : GlobalTheory.CxPts (i ≫ p) σ), y ∈ GlobalTheory.CxPts.ptsIn _ σ
      (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull u i)) := fun σ y => by
    rw [GlobalTheory.CxPts.mem_ptsIn]
    have e := hZ.under_eq_genericPoint y
    simp only [GlobalTheory.Cartier.under] at e
    rw [e]
    exact hu'
  refine ⟨_, GlobalTheory.Cartier.isRatSec_ratOfSec _ hu', ?_⟩
  rw [GlobalTheory.HermLB.curveDeg_sec (L := L) i _ hu' h0]
  refine sub_nonneg.2 (le_trans ?_ (finsum_nonneg fun z => mul_nonneg
    (by exact_mod_cast GlobalTheory.Cartier.mult_divOfSec_nonneg z) (Real.log_natCast_nonneg _)))
  rw [← neg_nonneg, ← finsum_neg_distrib]
  refine finsum_nonneg fun σ => ?_
  rw [← finsum_neg_distrib]
  refine finsum_nonneg fun y => ?_
  have h1 := hu1 σ (GlobalTheory.Points.PtsOver.map i rfl _ y)
  have h2 := GlobalTheory.Weight.nsq_nonneg (L.φ σ) (GlobalTheory.CxPts.secVal _ σ u) (GlobalTheory.Points.PtsOver.map i rfl _ y)
  have h3 := Real.log_nonpos h2 h1
  linarith

theorem isNef_shift_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → (L.shift (fun _ => t) (fun _ => rfl)).IsNef D := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s n w abelian₂ t hM hev hS ht
  have hw : ∀ j, w j ∈ W := fun j => (hS.gen _).2 (Submodule.subset_span ⟨j, rfl⟩)
  have hX : GlobalTheory.IsArithVar p D := hM.arith
  have hg := GlobalTheory.T.exists_nonzero_shortGenerator_section_imageModel K V Ω Nm W ev D X p L ψ s hM hev n w abelian₂ hS
  have hs := GlobalTheory.T.shortGenerator_sections_small_shifted_fubiniStudy K V Ω Nm W ev D X p L ψ s hM hev n w abelian₂ t hS ht
  refine ⟨(GlobalTheory.T.imageModel_metrics_semiPositive K V Ω Nm W ev D X p L ψ s hM hev).shift _ _, ?_, ?_⟩
  · refine GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX _ (GlobalTheory.isGenerated_of_finite (fun j => s ⟨w j, hw j⟩) ?_)
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨j, hj, hx⟩ := hg x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hx⟩
  · intro Z i _ _ _ hc hd
    exact horizontal_of_small _ X p D hX _ (fun x => by
      obtain ⟨j, hj, hx⟩ := hg x
      exact ⟨_, hs j hj, hx⟩) Z i hc hd

end GlobalTheory.ImageModel

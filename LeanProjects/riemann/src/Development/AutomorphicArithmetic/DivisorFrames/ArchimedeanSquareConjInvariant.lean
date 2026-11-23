import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

theorem UpperTheory.archimedean_square_conj_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (A : Over (Sp K)) [GrpObj A] (𝓛 : LB A.left) (m : ℕ) (v : Fin m → (epsR K ⟶ A)), 𝓛.IsLB → (∀ i, IsTangent (v i)) → ∀ (σ : K →+* ℂ) (N : ℝ), EigenvectorLieDegree.IsArchSq A 𝓛 v σ N → EigenvectorLieDegree.IsArchSq A 𝓛 v ((starRingEnd ℂ).comp σ) N := by
  rintro K _ _ A _ 𝓛 m v - ht σ N ⟨A', _, φ, g, u, Hm, χ, v', W, hφ, hA, hv, h0, hN⟩
  obtain ⟨A'', _, ψ, hc⟩ : ∃ (A'' : Over (Sp ℂ)) (_ : GrpObj A'') (ψ : A''.left ⟶ A'.left),
      IsGrpPullback A'' A' GlobalTheory.ArchMetricCompare.cj ψ :=
    ⟨_, _, _, isGrpPullback_pullback A' GlobalTheory.ArchMetricCompare.cj⟩
  choose v'' hv'' using fun k => (GlobalTheory.existsUnique_isVecOver (f := starRingEnd ℂ) hc.1 (v' k)).exists
  refine ⟨A'', inferInstance, ψ ≫ φ, g, GlobalTheory.ArchMetricCompare.cjUnif hc u, Hm.map star, _, v'', fun i => star (W i),
    (hc.comp hφ).congr (GlobalTheory.spMap_comp_spMap σ (starRingEnd ℂ)) rfl, GlobalTheory.ArchMetricCompare.cj_isAH hc u hA,
    fun i => ⟨GlobalTheory.CM.EllComp.isVecOver_comp (hv i).1 (hv'' i),
      GlobalTheory.ArchMetricCompare.cj_isDiff hc u ((hv i).1.isTangent hφ (ht i)) (hv'' i) (hv i).2⟩, h0, ?_⟩
  rw [← Complex.conj_ofReal N, hN, RingHom.map_det]
  congr 1
  ext i k
  simp [dotProduct, Matrix.mulVec, map_sum, Complex.star_def]

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

section
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexOrder ComplexConjugate

theorem cHess_posSemidef_of_levi {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    (cHess n (fun v => ((f v : ℝ) : ℂ)) x).PosSemidef := by
  classical
  set g : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hg
  have hg2 : ContDiffAt ℝ 2 g x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hgc : (fun w => conj (g w)) = g := funext fun w => by simp [g]
  have hH : (cHess n g x).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show conj (wd n k (wdb n j g) x) = wd n j (wdb n k g) x
    have h1 : (fun w => conj (wdb n j g w)) = wd n j g := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) x, h1, comm_wd_wdb g x hg2 j k]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  have hre : dotProduct (star y) (Matrix.mulVec (cHess n g x) y) = leviV n g x (fun k => conj (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self y
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · rw [hre]; exact hL _
  · simpa using him.symm

theorem re_sum_perm_det_nonneg {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    0 ≤ (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det).re := by
  have h := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hA).2
  have h0 : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have e : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det) =
      ((D.factorial : ℝ) : ℂ) * ReciprocityTheory.AnForm.mdisc A := by
    rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, Complex.ofReal_natCast, ← mul_assoc, mul_one_div_cancel h0, one_mul]
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) h

end

theorem dens_nonneg_of_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L : Fin D → MLine p σ} (h : ∀ i, (L i).φ.SemiPosReg D) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : 0 ≤ dens L c y :=
  mul_nonneg (by positivity) (re_sum_perm_det_nonneg (fun i => c.hess (L i).φ (pick (L i).φ.isLB y) y) fun i =>
    cHess_posSemidef_of_levi ((L i).cInf.contDiffAt c hy (mem_pick _ y)) (h i _ c y ⟨hy, mem_pick _ y⟩))

theorem part_neg_eq_zero_of_semiPosReg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  intro k _ X p σ _ D L h
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  have := dens_nonneg_of_semiPosReg h c (c.e.map_target hv)
  exact ENNReal.ofReal_eq_zero.2 (by simpa using this)

end GlobalTheory.Mix

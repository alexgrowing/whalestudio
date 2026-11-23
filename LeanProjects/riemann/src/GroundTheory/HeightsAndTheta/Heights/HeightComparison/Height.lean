import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCurve
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDegree
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightRecR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace HermLine

def standardPow (m : ι → ℕ) : HermLine n where
  deg k := m k
  metric z := ∏ k, l2Norm (z k) ^ m k
  metric_pos z hz := Finset.prod_pos fun k _ ↦ pow_pos (vectorL2Norm_pos (hz k)) _
  metric_smul c z _ _ := by
    simp only [vectorL2Norm_const_mul, mul_pow, Finset.prod_mul_distrib, zpow_natCast]
  metric_smooth := contDiffOn_prod fun k _ ↦ (contDiffOn_l2Norm_block k).pow _

end HermLine

theorem height_mul (A B : HermLine n) {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    height (A.mul B) x = height A x + height B x := by
  have hA := finite_support_height A x hx
  have hB := finite_support_height B x hx
  have hfin : (∑ᶠ v : FinitePlace (coordField x),
      ∑ k, ((A.mul B).deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))) =
      (∑ᶠ v : FinitePlace (coordField x),
        ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))) +
      ∑ᶠ v : FinitePlace (coordField x),
        ∑ k, (B.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i)) := by
    rw [← finsum_add_distrib hA hB]
    refine finsum_congr fun v ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [HermLine.mul, Pi.add_apply, Int.cast_add]
    ring
  have hinf : (∑ σ : coordField x →+* ℂ,
      Real.log ((A.mul B).metric fun k i ↦ σ (coordVec x k i))) =
      (∑ σ : coordField x →+* ℂ, Real.log (A.metric fun k i ↦ σ (coordVec x k i))) +
      ∑ σ : coordField x →+* ℂ, Real.log (B.metric fun k i ↦ σ (coordVec x k i)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    exact Real.log_mul (A.metric_pos _ (blockNonzero_sigma hx σ)).ne'
      (B.metric_pos _ (blockNonzero_sigma hx σ)).ne'
  unfold height
  rw [hfin, hinf]
  ring

def HeightAsIntersection.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ),
    Geo.IsIntersectionFamily II → ∀ (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x →
    height A x = II (orbitIdeal x) 1 ![A.toGeo] / Geo.degC (ι := blockIdx n) (orbitIdeal x)

theorem HeightAsIntersection.proof (h₁ : OrbitCurve.Statement) (h₂ : OrbitDegree.Statement)
    (h₃ : HeightRecR.Statement) : HeightAsIntersection.Statement := by
  intro ι _ _ _ n II hII A x hx
  obtain ⟨-, hAdd, hR⟩ := hII
  have hW : Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) (0 + 1) := h₁ ι n x hx
  have hdeg : (0 : ℝ) < Geo.degC (ι := blockIdx n) (orbitIdeal x) := by
    exact_mod_cast h₂ ι n x hx
  obtain ⟨c, hc⟩ := exists_chart hx
  have hsnoc : ∀ B : Geo.HermLine (blockIdx n),
      (Fin.snoc (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) B : Fin 1 → _) = ![B] := by
    intro B
    funext i
    fin_cases i
    rfl
  have hL : ∀ j : Fin 0, Geo.IsSmoothHerm ((Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) j) :=
    fun j ↦ j.elim0
  have key : ∀ (B : HermLine n) (d : ι → ℕ), (∀ k, B.deg k = d k) →
      II (orbitIdeal x) 1 ![B.toGeo] = Geo.degC (ι := blockIdx n) (orbitIdeal x) * height B x := by
    intro B d hd
    have h := hR (orbitIdeal x) 0 Fin.elim0 B.toGeo (chartMonomial c d) d hW hL
      B.isSmoothHerm_toGeo hd ((geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d))
      (chartMonomial_notMem_orbitIdeal x c hc d)
    rw [hsnoc] at h
    exact h.trans (h₃ ι n II B x _ hx (isSectionOn_chartMonomial B x c hc d hd))
  let m : ι → ℕ := fun k ↦ (A.deg k).natAbs
  have hB := key (HermLine.standardPow m) m fun k ↦ rfl
  have hAB := key (A.mul (HermLine.standardPow m)) (fun k ↦ (A.deg k + m k).toNat) fun k ↦ by
    simp only [HermLine.mul, HermLine.standardPow, Pi.add_apply, m]
    omega
  have hadd := hAdd (orbitIdeal x) 0 Fin.elim0 A.toGeo (HermLine.standardPow m).toGeo hW hL
    A.isSmoothHerm_toGeo (HermLine.standardPow m).isSmoothHerm_toGeo
  rw [hsnoc, hsnoc, hsnoc, ← HermLine.toGeo_mul] at hadd
  have hadd' : II (orbitIdeal x) 1 ![(A.mul (HermLine.standardPow m)).toGeo] =
      II (orbitIdeal x) 1 ![A.toGeo] + II (orbitIdeal x) 1 ![(HermLine.standardPow m).toGeo] :=
    hadd
  rw [hAB, hB, height_mul A _ hx] at hadd'
  rw [eq_div_iff hdeg.ne']
  linarith

end

end GroundTheory.Heights₂.Heights

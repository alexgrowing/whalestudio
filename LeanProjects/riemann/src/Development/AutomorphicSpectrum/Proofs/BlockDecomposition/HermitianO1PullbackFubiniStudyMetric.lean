import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Inhab

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem val_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    ((blockUnit i j h : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) =
      pullRatio (prB n k) W i (h.trans ((prB n k).preimage_mono inf_le_left)) j := by
  rw [← appLE_ratioOn (φ := prB n k) (W := W) (U := chart ℤ (n k) i ⊓ chart ℤ (n k) j)
    (i := i) (j := j) inf_le_left h]
  rfl

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W V : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (e : V ≤ W) :
    res e (blockUnit i j h) = blockUnit i j (e.trans h) := by
  refine Units.ext ?_
  rw [val_blockUnit]
  exact (congrArg (resG _ e) (val_blockUnit i j h)).trans (resG_pullRatio e)

theorem blockUnit_mul {k : Fin (m + 1)} (i j l : Bk n k) {W : (MP ℤ m n).Opens}
    (h₁ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (h₂ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) j ⊓ chart ℤ (n k) l))
    (h₃ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) l)) :
    blockUnit i j h₁ * blockUnit j l h₂ = blockUnit i l h₃ := by
  refine Units.ext ?_
  rw [Units.val_mul, val_blockUnit, val_blockUnit, val_blockUnit]
  exact pullRatio_mul_pullRatio

theorem valR_pullRatio (x : Sp ℂ ⟶ MP ℤ m n) {k : Fin (m + 1)} (i j : Bk n k)
    (h : ⊤ ≤ x ⁻¹ᵁ blockChart n k i) :
    valR x (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) =
      valR (x ≫ prB n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) := by
  have h' : ⊤ ≤ (x ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) i := h
  rw [valR, valR, dif_pos h, dif_pos h', pullRatio,
    ← Scheme.Hom.appLE_comp_appLE x (prB n k) (chart ℤ (n k) i) (blockChart n k i) ⊤ le_rfl h]
  rfl

theorem norm_eq_fs {ι : Type} [Fintype ι] (w : ι → ℂ) (i c : ι) (hi : w i ≠ 0) (hc : w c ≠ 0) :
    ‖WithLp.toLp 2 w‖ =
      ‖w c‖ * ‖w i / w c‖ * Real.exp (Real.log (∑ a, ‖w a / w i‖ ^ 2) / 2) := by
  have hi' : 0 < ‖w i‖ := norm_pos_iff.2 hi
  have hc' : 0 < ‖w c‖ := norm_pos_iff.2 hc
  have hS : ∑ a, ‖w a / w i‖ ^ 2 = (∑ a, ‖w a‖ ^ 2) / ‖w i‖ ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by rw [norm_div, div_pow]
  have hT : 0 < ∑ a, ‖w a‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  have hpos : 0 < ∑ a, ‖w a / w i‖ ^ 2 := by rw [hS]; positivity
  have hexp : Real.exp (Real.log (∑ a, ‖w a / w i‖ ^ 2) / 2) = √(∑ a, ‖w a / w i‖ ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
    congr 1
    ring
  rw [hexp, hS, Real.sqrt_div hT.le, Real.sqrt_sq hi'.le, norm_div, EuclideanSpace.norm_eq]
  simp only [PiLp.toLp_apply]
  field_simp

theorem pullback_O1_transition_eq_blockUnit (k : Fin (m + 1)) (i j : PUnit → Fin (n k + 1))
    (h : ((O1 ℤ (n k)).pull (prB n k)).U i ⊓ ((O1 ℤ (n k)).pull (prB n k)).U j ≤
      prB n k ⁻¹ᵁ (chart ℤ (n k) (i PUnit.unit) ⊓ chart ℤ (n k) (j PUnit.unit))) :
    ((O1 ℤ (n k)).pull (prB n k)).g i j = blockUnit (i PUnit.unit) (j PUnit.unit) h := by
  refine (linComb_punit_g (O1 ℤ (n k)) (prB n k) 1 i j).trans ?_
  rw [zpow_one]
  rfl

theorem prod_blockUnit_single {W : (MP ℤ m n).Opens} (k : Fin (m + 1)) (c c' : ∀ k, Bk n k)
    (h : ∀ k', W ≤ prB n k' ⁻¹ᵁ (chart ℤ (n k') (c k') ⊓ chart ℤ (n k') (c' k'))) :
    (∏ k', blockUnit (c k') (c' k') (h k') ^ (Pi.single k (1 : ℤ) : Fin (m + 1) → ℤ) k') =
      blockUnit (c k) (c' k) (h k) := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]

theorem ev_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (e : W ≤ blockChart n k i)
    {y : CxPts (mpStr ℤ m n) σ₀} (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) :
    CxPts.ev (mpStr ℤ m n) σ₀ W (blockUnit i j h : Γ(MP ℤ m n, W)ˣ).val y =
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y := by
  rw [val_blockUnit, ← resG_pullRatio (hi := le_rfl) e, CxPts.ev_res _ hy]

theorem ofMetrics_single_h (k : Fin (m + 1)) (z : (Σ k, Bk n k) → ℂ) :
    (Geo.HermLine.ofMetrics (fun k => Geo.fsMetric (Bk n k)) (Pi.single k 1)).h z =
      ‖WithLp.toLp 2 fun a => z ⟨k, a⟩‖ := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]
    rfl

theorem prod_norm_single (k : Fin (m + 1)) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (∏ k', ‖z ⟨k', c k'⟩‖ ^ (Pi.single k (1 : ℤ) : Fin (m + 1) → ℤ) k') = ‖z ⟨k, c k⟩‖ := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]

end GlobalTheory.CompanionTheory.MPDict.Inhab

open GlobalTheory.CompanionTheory.MPDict.Inhab in

theorem GlobalTheory.CompanionTheory.MPDict.isHermRep_pullback_hermitian_O1 : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)), IsHermRep ((hermitianTwistingSheaf ℤ (n k)).pull (prB n k) (pr_toSpecBase ℤ m n k)) (Geo.HermLine.ofMetrics (fun k => Geo.fsMetric (Bk n k)) (Pi.single k 1)) := by
  intro m n k
  have hU (i : PUnit → Fin (n k + 1)) : ((O1 ℤ (n k)).pull (prB n k)).U i ≤ blockChart n k (i PUnit.unit) :=
    LB.wchart_le (O1 ℤ (n k)) (fun _ => prB n k) i PUnit.unit
  refine ⟨fun i c => blockUnit (c k) (i PUnit.unit) (le_inf (inf_le_right.trans (mchart_le c k))
    (inf_le_left.trans (hU i))), ?_, ?_, ?_⟩
  · intro i j c
    change Semi.res _ _ = Semi.res _ (((O1 ℤ (n k)).pull (prB n k)).g i j) * Semi.res _ _
    beta_reduce
    rw [pullback_O1_transition_eq_blockUnit k i j (fun x hx => ⟨hU i hx.1, hU j hx.2⟩)]
    refine (res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (res_blockUnit _ _ _ _) (res_blockUnit _ _ _ _)).symm)
    rw [mul_comm]
    exact (blockUnit_mul _ _ _ _ _ _).symm
  · intro i c c'
    beta_reduce
    refine (res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (res_blockUnit _ _ _ _) (prod_blockUnit_single k c c' _)).symm)
    rw [mul_comm]
    exact (blockUnit_mul _ _ _ _ _ _).symm
  · intro i c y z hz hy
    have hy₁ : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (i PUnit.unit)) :=
      ptsIn_mono (inf_le_left.trans (hU i)) hy
    have hy₂ : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) :=
      ptsIn_mono (inf_le_right.trans (mchart_le c k)) hy
    have hi : z ⟨k, i PUnit.unit⟩ ≠ 0 := ((hz k _).1).1 hy₁
    have hc : z ⟨k, c k⟩ ≠ 0 := ((hz k _).1).1 hy₂
    have hφ : (((hermitianTwistingSheaf ℤ (n k)).pull (prB n k) (pr_toSpecBase ℤ m n k)).φ σ₀).φ i y =
        Real.log (∑ a, ‖z ⟨k, a⟩ / z ⟨k, i PUnit.unit⟩‖ ^ 2) := by
      refine (Weight.pull_φ (ProjAn.fsO1 ℤ σ₀ (n k)) (prB n k) (pr_toSpecBase ℤ m n k) i y).trans ?_
      refine (Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ (Finset.sum_congr rfl fun a _ => ?_))
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      refine congrArg (‖·‖ ^ 2) (Eq.trans ?_ ((hz k (i PUnit.unit)).2 a hy₁))
      exact (valR_pullRatio y.1 (i PUnit.unit) a hy₁).symm
    have hev : CxPts.ev (mpStr ℤ m n) σ₀ (((hermitianTwistingSheaf ℤ (n k)).pull (prB n k) (pr_toSpecBase ℤ m n k)).B.U i ⊓ mchart c)
        (blockUnit (c k) (i PUnit.unit) (le_inf (inf_le_right.trans (mchart_le c k))
          (inf_le_left.trans (hU i))) : Γ(MP ℤ m n, _)ˣ).val y =
        z ⟨k, i PUnit.unit⟩ / z ⟨k, c k⟩ := by
      exact (ev_blockUnit _ _ _ (inf_le_right.trans (mchart_le c k)) hy).trans ((hz k (c k)).2 _ hy₂)
    refine (ofMetrics_single_h k z).trans ?_
    refine (norm_eq_fs (fun a => z ⟨k, a⟩) (i PUnit.unit) (c k) hi hc).trans ?_
    rw [hφ]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_norm_single k c z).symm (congrArg _ hev.symm)) rfl

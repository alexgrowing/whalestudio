import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMetricUnitaryGauge
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSAmp.GenMap

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem mem_chart {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
  Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))

theorem loc_mul_div (P : Pair p) (e : ℕ) (f ρ : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc e 0 f i j * (ρ / P.loc e 0 1 i j) = f * ρ := by
  have := (P.r i).ne_zero
  have := (P.r' j).ne_zero
  simp only [Pair.loc]
  field_simp

theorem loc_eq_mul_inv (P : Pair p) (e : ℕ) (f ρ : X.functionField) (hρ : ρ ≠ 0) (i : P.L.B.ι)
    (j : P.A.B.ι) : P.loc e 0 f i j = f * ρ * (ρ / P.loc e 0 1 i j)⁻¹ := by
  have := (P.r i).ne_zero
  have := (P.r' j).ne_zero
  simp only [Pair.loc]
  field_simp

theorem exists_secs (P : Pair p) {D e : ℕ} {x : Fin (D + 1) → X.functionField} (hx : Gens P D e x) :
    ∃ (ρ : (P.L.pow e).B.ι → X.functionFieldˣ) (s : Fin (D + 1) → (P.L.pow e).B.Sec),
      (∀ z c i j, z ∈ (P.L.pow e).B.U c → z ∈ P.L.B.U i → z ∈ P.A.B.U j →
        UnitAt z ((ρ c : X.functionField) / P.loc e 0 1 i j)) ∧
      (∀ (σ : k →+* ℂ) (y : CxPts p σ) c j, y ∈ ptsIn p σ ((P.L.pow e).B.U c) → y ∈ ptsIn p σ (P.A.B.U j) →
        ‖ratVal ((ρ c : X.functionField) / P.loc e 0 1 (c PUnit.unit) j) y‖ = 1) ∧
      ∀ l c (hc : genericPoint X ∈ (P.L.pow e).B.U c), fnOf _ hc ((s l).f c) = x l * ρ c := by
  obtain ⟨ρ, hρ, hu, hn⟩ := Pair.rep_pow k X p P 1 0 P.L e (Pair.rep_base k X p P).1
  simp only [mul_one, mul_zero] at hu hn
  have hs : ∀ l, ∃ u : (P.L.pow e).B.Sec, ∀ c (hc : genericPoint X ∈ (P.L.pow e).B.U c),
      fnOf _ hc (u.f c) = x l * ρ c := fun l =>
    RepDict.exists_sec hρ fun c z hz => by
      obtain ⟨i, hi⟩ := mem_chart P.L.isLB z
      obtain ⟨j, hj⟩ := mem_chart P.A.isLB z
      rw [← loc_mul_div P e (x l) _ i j]
      exact (hx.mem l z i j hi hj).mul (hu z c i j hz hi hj).regAt
  choose s hs using hs
  refine ⟨ρ, s, hu, fun σ y c j hc hj => ?_, hs⟩
  have hc' := mem_pow_iff.1 hc
  have hU := hu _ c _ j (mem_ptsIn.1 hc) (mem_ptsIn.1 hc') (mem_ptsIn.1 hj)
  have h1 := hn σ y c _ j hc hc' hj
  have h2 : ((P.L.pow e).φ σ).φ c y = ((e : ℤ) : ℝ) * (P.L.φ σ).φ (c PUnit.unit) y := Weight.zpow_φ _ _ _ _
  rw [h2] at h1
  push_cast at h1
  refine Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 (ratVal_ne_zero hU)) ?_
  linarith

end GlobalTheory.HSAmp.GenMap

namespace GlobalTheory.HSAmp.GenMap

theorem toProj_gens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → x 0 ≠ 0 → ∃ (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  intro k _ X _ p D _ P e x hx hx0
  obtain ⟨ρ, s, hu, hn1, hs⟩ := exists_secs P hx
  have hnz : ∀ l z i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j →
      (z ∈ Out.nonzeroLocus (s l) ↔ UnitAt z (P.loc e 0 (x l) i j)) := by
    intro l z i j hi hj
    obtain ⟨c, hc⟩ := mem_chart (P.L.pow e).isLB z
    have hU := hu z c i j hc hi hj
    rw [mem_nonzeroLocus_iff (s l) c hc, ← unitAt_fnOf_iff hc (gen_mem hc), hs l c (gen_mem hc)]
    exact ⟨fun h => loc_eq_mul_inv P e (x l) _ (ρ c).ne_zero i j ▸ h.mul hU.inv,
      fun h => loc_mul_div P e (x l) _ i j ▸ h.mul hU⟩
  have hcov : ⨆ l, Out.nonzeroLocus (s l) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨i, hi⟩ := mem_chart P.L.isLB z
    obtain ⟨j, hj⟩ := mem_chart P.A.isLB z
    obtain ⟨l, hl⟩ := hx.cover z
    exact Opens.mem_iSup.2 ⟨l, (hnz l z i j hi hj).2 (hl i j hi hj)⟩
  obtain ⟨c, hc⟩ := mem_chart (P.L.pow e).isLB (genericPoint X)
  have hη : genericPoint X ∈ Out.nonzeroLocus (s 0) := by
    rw [mem_nonzeroLocus_iff (s 0) c hc, X.mem_basicOpen _ _ hc]
    show IsUnit (fnOf _ hc ((s 0).f c))
    rw [hs 0 c hc]
    exact isUnit_iff_ne_zero.2 (mul_ne_zero hx0 (ρ c).ne_zero)
  have hpre := ProjSpace.toProj_preimage_chart p s hcov 0
  have hmem : genericPoint X ∈ ProjSpace.toProj p s hcov ⁻¹ᵁ ProjSpace.chart k D 0 := by
    rw [hpre]; exact hη
  refine ⟨ProjSpace.toProj p s hcov, ProjSpace.toProj_str p s hcov, ⟨hmem, fun j => ?_⟩, fun u hu' => ?_⟩
  · change fnOf _ hmem _ = _
    rw [ProjSpace.pullRatio_toProj_on p s hcov 0 j le_rfl, fnOf_resG]
    have hc' : genericPoint X ∈ Out.nonzeroLocus (s 0) ⊓ (P.L.pow e).B.U c := ⟨hη, hc⟩
    have e1 := congrArg (fnOf _ hc') (ProjSpace.secRatio_spec (s 0) (s j) c)
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hs j c hc, hs 0 c hc] at e1
    rw [eq_div_iff hx0]
    refine mul_right_cancel₀ (ρ c).ne_zero ?_
    linear_combination -e1
  · have he : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hx.pos.ne'
    refine (HermLB.isometric_pull_fs_toProj k X p ((up P.L u).pow e) D s hcov (fun _ => 1) (fun _ => by simp)
      (fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩) ?_).symm
    intro σ i y hy
    change y ∈ ptsIn p σ ((P.L.pow e).B.U i) at hy
    have hy' : y ∈ ptsIn p σ (P.L.B.U (i PUnit.unit)) := mem_pow_iff.1 hy
    have hj : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
    have hg := hn1 σ y i _ hy hj
    have hA : ∀ l, ‖valR y.1 ((P.L.pow e).B.U i) ((s l).f i)‖ =
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ := fun l => by
      have hη := gen_mem (mem_ptsIn.1 hy)
      change ‖ev p σ _ ((s l).f i) y‖ = _
      rw [← ratVal_fnOf hy hη, hs l i hη, ← loc_mul_div P e (x l) _ (i PUnit.unit) _,
        ratVal_mul (hx.mem l _ _ _ (mem_ptsIn.1 hy') (mem_ptsIn.1 hj))
          (hu _ i _ _ (mem_ptsIn.1 hy) (mem_ptsIn.1 hy') (mem_ptsIn.1 hj)).regAt, norm_mul, hg, mul_one]
    have hnu : ∀ l, P.nu e 0 σ y (x l) ^ 2 =
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2 *
          Real.exp (-((e : ℝ) * (P.L.φ σ).φ (i PUnit.unit) y)) := fun l => by
      rw [nu_eq k X p P e 0 (x l) (hx.mem l) σ y _ _ hy' hj, mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    set S := ∑ l, ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2 with hS
    have hSpos : 0 < S := by
      obtain ⟨l, hl⟩ := hx.cover (under y)
      have h0 := norm_pos_iff.2 (ratVal_ne_zero (hl _ _ (mem_ptsIn.1 hy') (mem_ptsIn.1 hj)))
      exact (pow_pos h0 2).trans_le (Finset.single_le_sum (f := fun l =>
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ l))
    have hsum : ∑ l, P.nu e 0 σ y (x l) ^ (2 * 1) = Real.exp (-((e : ℝ) * (P.L.φ σ).φ (i PUnit.unit) y)) * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_one, hnu l, mul_comm]
    have hu1 := hu' σ y
    rw [hsum, Real.log_mul (Real.exp_pos _).ne' hSpos.ne', Real.log_exp] at hu1
    change (((P.L.φ σ).addFn (u.u σ)).zpow (e : ℤ)).φ i y = _
    refine (Weight.zpow_φ _ _ _ _).trans ?_
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    change ((e : ℤ) : ℝ) * ((P.L.φ σ).φ (i PUnit.unit) y + u.u σ y) =
      Real.log (∑ l, ‖valR y.1 ((P.L.pow e).B.U i) ((s l).f i)‖ ^ 2)
    simp only [hA, ← hS]
    rw [hu1]
    push_cast
    field_simp
    ring

end GlobalTheory.HSAmp.GenMap

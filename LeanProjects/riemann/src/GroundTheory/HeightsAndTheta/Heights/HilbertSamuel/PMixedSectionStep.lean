import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedSectionStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionMixed
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIntegralAgainstPositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionMixed
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftNefBig
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace MixedSectionInduction

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

theorem cycR_eq_finsum (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    cycR I P L s = ∑ᶠ W : Ideal (MRing ι), (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℝ) *
      (if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)) := by
  unfold cycR
  rw [finsum_mem_def]
  congr 1
  funext W
  by_cases hW : W ∈ divSupp P s
  · rw [Set.indicator_of_mem hW, GroundTheory.Heights₂.Heights.Inter.divCycle_apply_of_mem hW]
  · rw [Set.indicator_of_notMem hW, GroundTheory.Heights₂.Heights.Inter.divCycle_apply_of_not_mem hW]
    simp

end MixedSectionInduction

open MixedSectionInduction in

theorem MixedSectionStep.proof (hS : SmallSectionMixed.Statement) (hR : GroundTheory.Heights₂.Heights.Inter.RatR.Statement)
    (hI : IntegralAgainstPositive.Statement) (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg)
    (hE : ZCombExpand.Statement) : MixedSectionStep.Statement := by
  classical
  intro K _ ι _ P P0 d M H II hII hd hP hP0 hMs hMn hMc hMW hHa hHs hHb hHc hAt q p hp hpos
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  change MixedKleiman.AtDim n at hAt
  have hn : 1 ≤ n := by omega
  obtain ⟨m, f, g, hm, hfg, hdiv, hbd⟩ :=
    hS K ι P P0 (n + 1) M H p q II hII (by omega) hP hP0 hMs hMn hMc hHa hHs hHb hHc hp hpos
  have hMsm : IsSmoothHerm M := hMs.1
  have hHsm : IsSmoothHerm H := hHs.1
  let L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)
  let F : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)
  have hLsp : ∀ j, IsSemipositiveRel P0 P (L j) := fun j => by
    simp only [L]
    split_ifs
    · exact hMs
    · exact SmallSectionMixedAlt.isSemipositiveRel_zcomb hMs hHs q p
  have hFs : ∀ j, IsSmoothHerm (F j) := fun j => by
    simp only [F]
    split_ifs
    · exact hMsm
    · exact ZCombLimit.isSmoothHerm_zcomb_int hMsm hHsm _ _
  have hsnoc : ∀ X, Fin.snoc L X = Function.update F (Fin.last n) X := by
    intro X
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Function.update_self]
    · rw [Fin.snoc_castSucc, Function.update_of_ne (Fin.castSucc_lt_last i).ne]
      rfl
  have hFN : Function.update F (Fin.last n) (HermLine.zcomb M H (q : ℤ) (p : ℤ)) = F := by
    funext j
    by_cases hj : j = Fin.last n
    · subst hj
      rw [Function.update_self]
      simp only [F, Fin.val_last]
      rw [if_neg (by omega)]
    · rw [Function.update_of_ne hj]

  have hscale : II K ι P (n + 1) (Fin.snoc L (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ))) =
      (m : ℝ) * II K ι P (n + 1) F := by
    have e1 := ZCombLimit.fam_update_zcomb_int (hII K ι) hP F hFs (Fin.last n) hMsm hHsm
      ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)
    have e2 := ZCombLimit.fam_update_zcomb_int (hII K ι) hP F hFs (Fin.last n) hMsm hHsm (q : ℤ) (p : ℤ)
    rw [hFN] at e2
    rw [hsnoc, e1, e2]
    push_cast
    ring
  have hpts : ∀ {W : Ideal (MRing ι)}, P ≤ W → mcPts W ⊆ mcPts P := fun hPW z hz =>
    ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hchar : ∀ W W' : Ideal (MRing ι), W ≤ W' → charOf W ≠ 0 → charOf W' ≠ 0 := by
    intro W W' hle hW hW'
    apply hW
    unfold charOf at hW' ⊢
    rw [Int.natAbs_eq_zero, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at hW' ⊢
    exact le_bot_iff.mp (hW' ▸ Ideal.comap_mono hle)
  obtain ⟨α, β, hfα, hgβ, hfP, hgP, hαβ⟩ := hfg

  have key : ∀ W ∈ divSupp P f, 0 ≤ (if IsHorizontal W then II K ι W n L
      else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)) := by
    intro W hW
    obtain ⟨hH, hV⟩ := divSuppArith K ι P n
      (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (α k : ℤ))) f W hP ⟨α, fun _ => rfl, hfα, hfP⟩ hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    split_ifs with hWh
    ·
      have hWv := hH hWh
      rw [(hE K ι (II K ι) (hII K ι) W n M H q p hWv hMsm hHsm).2 hn]
      refine Finset.sum_nonneg fun i hi => mul_nonneg (by positivity) ?_
      have hi' := Finset.mem_range.mp hi
      exact hAt K ι W P0 M H (fun _ => 1) II hII hn hWv (hP0.trans hPW)
        ⟨hMsm, fun z hz => hMs.2 z (hpts hPW hz)⟩ (fun W' h1 h2 => hMn W' h1 (hPW.trans h2)) hMc
        (fun W' h1 h2 => hMW W' h1 (hPW.trans h2)) (by rw [hHa]; funext k; simp)
        ⟨hHsm, fun z hz => hHs.2 z (hpts hPW hz)⟩ (fun z hz => hHb z (hpts hPW hz)) hHc (n - i) (by omega)
    ·
      by_cases hc : charOf W = 0
      · simp [hc]
      have hg : 0 ≤ geoNum n W (fun j => (L j).a) := by
        refine hK K ι W n _ (hV hWh).1 hc (hV hWh).2.2 fun j => ?_
        intro W' h1 h2 h3
        have hM' : 0 ≤ geoNum 1 W' (fun _ => M.a) := hMn W' h1 (hPW.trans h2) (hchar W W' h2 hc) h3
        simp only [L]
        split_ifs
        · exact hM'
        · show 0 ≤ geoNum 1 W' (fun _ => (q : ℤ) • M.a + (p : ℤ) • H.a)
          rw [ShiftedNefBig.geoNum_one_add]
          have hH' : 0 ≤ geoNum 1 W' (fun _ => (p : ℤ) • H.a) :=
            ProjLine.nefOnFibres_of_nonneg W' _ (fun k => by rw [hHa]; simp) W' h1 le_rfl
              (hchar W W' h2 hc) h3
          exact add_nonneg (mul_nonneg (Nat.cast_nonneg q) hM') hH'
      exact mul_nonneg (by exact_mod_cast hg) (Real.log_natCast_nonneg _)

  have hcyc : cycR (II K ι) P L g ≤ cycR (II K ι) P L f := by
    rw [cycR_eq_finsum, cycR_eq_finsum]
    refine finsum_le_finsum' ?_ ?_ fun W => ?_
    · exact Set.Finite.subset (Finsupp.hasFiniteSupport (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g)) fun W hW h => hW (by simp [h])
    · exact Set.Finite.subset (Finsupp.hasFiniteSupport (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f)) fun W hW h => hW (by simp [h])
    · have hle : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g W ≤ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W := hdiv W
      by_cases hW : W ∈ divSupp P f
      · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (key W hW)
      · have h0 : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W = 0 := GroundTheory.Heights₂.Heights.Inter.divCycle_apply_of_not_mem hW
        rw [h0] at hle ⊢
        rw [Nat.le_zero.mp hle]

  have hint : ptsIntegral P (pot L)
      (logNormRat (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)) f g) ≤ 0 := by
    refine hI K ι P P0 n L _ hP0 hLsp fun z hz => ?_
    have hpos := (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)).pos z hz.1
    unfold logNormRat
    refine Real.log_nonpos (by positivity) ((div_le_one hpos).mpr ?_)
    by_cases hg0 : ‖eval z (map (Int.castRingHom ℂ) g)‖ = 0
    · rw [hg0, div_zero]
      exact hpos.le
    · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0))]
      linarith [hbd z hz]
  have hNm : IsSmoothHerm (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)) :=
    ZCombLimit.isSmoothHerm_zcomb_int hMsm hHsm _ _
  have hrec := hR K ι (II K ι) (hII K ι) P n L _ f g hP (fun j => (hLsp j).1) hNm
    ⟨α, β, hfα, hgβ, hfP, hgP, hαβ⟩
  rw [hscale] at hrec
  have hnn : 0 ≤ (m : ℝ) * II K ι P (n + 1) F := by
    rw [hrec]
    unfold recRRat
    linarith
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm : (0 : ℝ) < m)).mp hnn

end GroundTheory.Heights₂.Heights.HilbertSamuel

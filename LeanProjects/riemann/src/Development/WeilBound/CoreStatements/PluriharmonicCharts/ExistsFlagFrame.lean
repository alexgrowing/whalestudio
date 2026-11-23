import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorColsBEqZero
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem detFac_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) :
    detFac j i (T.map f) = f (detFac j i T) := by
  unfold detFac
  rw [CPts.minorIJ_map, CPts.minorIJ_map]
  split_ifs <;> simp

theorem muI_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) :
    muI N j i (T.map f) = f (muI N j i T) := by
  unfold muI
  rw [CPts.minorIJ_map]
  split_ifs <;> simp

theorem zpow_sum' {σ : Type} (S : Finset σ) {x : L} (hx : x ≠ 0) (n : σ → ℤ) : x ^ (∑ p ∈ S, n p) = ∏ p ∈ S, x ^ n p := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

theorem chartMono_ne {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (e : K → ℤ) :
    chartMono z c e ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)

theorem chartMono_eDeg {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (τ : Ψ) (a : Fin N) (k₀ : K) :
    chartMono z c (eDeg M τ a k₀) * (z ⟨k₀, c k₀⟩ ^ 2 * ∏ i, chartMono z c (M.dy (τ, i)) ^ xiCoef τ a (τ, i)) = 1 := by
  rw [← prod_xi_pair τ a fun p => chartMono z c (M.dy p)]
  have e1 : ∏ p, chartMono z c (M.dy p) ^ xiCoef τ a p = ∏ k, z ⟨k, c k⟩ ^ ∑ p, xiCoef τ a p * M.dy p k := by
    simp only [chartMono, ← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_sum' _ (hc k)]
    exact Finset.prod_congr rfl fun p _ => by rw [← _root_.zpow_mul, mul_comm]
  have e2 : z ⟨k₀, c k₀⟩ ^ 2 = ∏ k, z ⟨k, c k⟩ ^ (if k = k₀ then (2 : ℤ) else 0) := by
    rw [Finset.prod_eq_single k₀ (fun k _ h => by rw [if_neg h, zpow_zero]) (by simp), if_pos rfl, zpow_ofNat]
  rw [e1, e2, chartMono, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [← zpow_add₀ (hc k), ← zpow_add₀ (hc k), eDeg]
  rw [show -(∑ p, xiCoef τ a p * M.dy p k) - (if k = k₀ then 2 else 0) + ((if k = k₀ then 2 else 0) +
    ∑ p, xiCoef τ a p * M.dy p k) = 0 by ring, zpow_zero]

theorem chartMono_dy (z : (Σ k, ι k) → L) (c : ∀ k, ι k) (p : Ψ × Fin N) :
    chartMono z c (M.dy p) = (∏ k : NonPluckerBlocks M.blk, (z ⟨k.1, c k.1⟩ ^ M.b p k)⁻¹) *
      (M.blk p).elim 1 fun k => z ⟨k, c k⟩ := by
  rw [chartMono, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => ∀ p', M.blk p' ≠ some k)]
  congr 1
  · rw [Finset.prod_subtype (p := fun k => ∀ p', M.blk p' ≠ some k) _ (by simp)]
    refine Finset.prod_congr (by congr) fun k _ => ?_
    rw [FlagModel.dy, dif_pos k.2, _root_.zpow_neg]
  · cases hp : M.blk p with
    | none =>
      refine Finset.prod_eq_one fun k hk => ?_
      rw [FlagModel.dy, dif_neg (Finset.mem_filter.1 hk).2, hp, if_neg (by simp), zpow_zero]
    | some k₁ =>
      have hk₁ : ¬ ∀ p', M.blk p' ≠ some k₁ := fun h => h p hp
      rw [Finset.prod_eq_single k₁ (fun k hk h => by
        rw [FlagModel.dy, dif_neg (Finset.mem_filter.1 hk).2, hp, if_neg (by simpa using h.symm), zpow_zero])
        (fun h => (h (Finset.mem_filter.2 ⟨Finset.mem_univ k₁, hk₁⟩)).elim), FlagModel.dy, dif_neg hk₁, if_pos hp,
        zpow_one]
      rfl

theorem blk_some {i : Fin N} (τ : Ψ) (hi : IsProperStep N j i) : ∃ k, M.blk (τ, i) = some k :=
  Option.ne_none_iff_exists'.1 fun h => (M.blk_none _).1 h hi

theorem isPt_base {z : (Σ k, ι k) → L} (hz : IsPt y z) : IsPt M.x (basePart M.blk z) :=
  hz.comp (CPts.blockMap_base M) (algebraMap M.Ω Φ) (funext M.y_base)

theorem hasVal_base {z : (Σ k, ι k) → L} {s : M.Ω} {v : L} (h : HasVal M.x (basePart M.blk z) s v) :
    HasVal y z (algebraMap M.Ω Φ s) v :=
  HasVal.pull (CPts.blockMap_base M) (algebraMap M.Ω Φ) (funext M.y_base) h

theorem chart_ne {z : (Σ k, ι k) → L} {F : FrameData ι Ψ N M.Ω M.blk}
    (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z))) (k : NonPluckerBlocks M.blk) : z ⟨k.1, F.c k⟩ ≠ 0 := fun h =>
  hG.1 k ((mem_iff_of_homog (isMultiHomog_X _)).2 (by rw [aeval_X]; exact h))

theorem exists_flag_frame (τ : Ψ) {z : (Σ k, ι k) → L} (hz : IsPt y z) {F : FrameData ι Ψ N M.Ω M.blk}
    (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z))) :
    ∃ (b : Matrix (Fin N) (Fin N) Φ) (H H' : Matrix (Fin N) (Fin N) (regO y z)), IsBlockDiag j b ∧
      b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧ IsBlockDiag j H ∧ H' * H = 1 ∧
      (F.T τ).map (algebraMap M.Ω Φ) * H.map (regO y z).subtype = M.g τ * b := by
  haveI := isLocalRing_regO hz
  let am := algebraMap M.Ω Φ
  let h := (F.T τ)⁻¹.map am * M.g τ
  have hTh : (F.T τ).map am * h = M.g τ := CPts.map_mul_inv_map am (hF.1 τ).2 _
  have hhb : IsBlockDiag j h := (((hF.1 τ).1.inv (hF.1 τ).2.isUnit).map am).mul (M.g_block τ)
  have hhd : h.det ≠ 0 := fun e => (M.isUnit_det_g τ).ne_zero (by rw [← hTh, det_mul, e, mul_zero])
  have hu : ∀ q I, am (F.u q I) ∈ regO y z := fun q I =>
    (exists_hasVal_of_regAt (hG.2.1 q I).1).imp fun _ => hasVal_base M
  have hu' : ∀ I q, am (F.u' I q) ∈ regO y z := fun I q =>
    (exists_hasVal_of_regAt (hG.2.1 q I).2).imp fun _ => hasVal_base M
  obtain ⟨b, hb, hbt, hbd, hO, hO'⟩ := exists_local_frame (regO y z) M.j_le h hhb hhd fun i hi => by
    obtain ⟨k, hk⟩ := blk_some M τ hi
    obtain ⟨c, hc⟩ := hz.1 k
    have hyc := hz.coord_ne hc
    have hdet : am (detFac j i (F.T τ)) ≠ 0 :=
      (map_ne_zero am).2 (CPts.detFac_ne_zero M.j_le i (hF.1 τ).1 (hF.1 τ).2)
    have hE : am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k') ≠ 0 := (map_ne_zero am).2
      (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (M.x_chart_ne (isPt_base M hz).le hG k'))
    let η := am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k') / (am (detFac j i (F.T τ)) * y ⟨k, c⟩)
    have rel : ∀ m, η * ∑ I, am (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j i) = y ⟨k, m⟩ / y ⟨k, c⟩ := fun m => by
      have := CPts.frame_gen M hF (RingHom.id Φ) hk m hhb isBlockDiag_one blockTriangular_one
        (by rw [mul_one]; exact hTh)
      simp only [RingHom.id_apply, Matrix.one_apply_eq, Finset.prod_const_one, mul_one] at this
      simp only [η]
      rw [div_mul_eq_mul_div, ← this]
      exact mul_div_mul_left _ _ hdet
    have hO : ∀ I, η * minorIJ h I (stepCols N j i) ∈ regO y z := fun I => by
      by_cases hI : IsStepRows N j i I
      · rw [← dual_sum i (fun m I => am (F.u ⟨k, m⟩ I)) (fun I m => am (F.u' I ⟨k, m⟩)) (fun I I' h1 h2 => by
          have := congrArg am (hF.2.2.1 (τ, i) k hk I I' h1 h2)
          rw [map_sum] at this
          simp only [map_mul] at this
          rw [this]
          split_ifs <;> simp) (fun I => minorIJ h I (stepCols N j i))
          (fun I hI => minor_stepCols_eq_zero M.j_le h I hhb hI) I hI, Finset.mul_sum]
        refine sum_mem fun m _ => ?_
        rw [mul_left_comm, rel]
        exact mul_mem (hu' _ _) ⟨_, hasVal_ratio hz m c hc⟩
      · rw [minor_stepCols_eq_zero M.j_le h I hhb hI, mul_zero]; exact zero_mem _
    refine ⟨η, div_ne_zero hE (mul_ne_zero hdet hyc), hO, ?_⟩
    have h1 : ∑ I, (⟨_, hu ⟨k, c⟩ I⟩ : regO y z) * ⟨_, hO I⟩ = 1 := Subtype.ext (by
      have := rel c
      rw [div_self hyc, Finset.mul_sum] at this
      simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, Subring.coe_one]
      rw [← this]
      exact Finset.sum_congr rfl fun I _ => by ring)
    have h2 := congrArg (valO hz) h1
    rw [map_sum, map_one] at h2
    obtain ⟨I, -, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h2.trans_ne one_ne_zero)
    rw [map_mul] at hI
    have h3 := hasVal_valO hz ⟨_, hO I⟩
    exact ⟨I, h3.ne_zero hz (right_ne_zero_of_mul hI), _, h3.inv hz (right_ne_zero_of_mul hI)⟩
  have hd : (h * b).det ≠ 0 := by
    rw [det_mul, det_of_upperTriangular hbt]
    exact mul_ne_zero hhd (Finset.prod_ne_zero_iff.2 fun a _ => hbd a)
  let H : Matrix (Fin N) (Fin N) (regO y z) := Matrix.of fun a c => ⟨_, hO a c⟩
  let H' : Matrix (Fin N) (Fin N) (regO y z) := Matrix.of fun a c => ⟨_, hO' a c⟩
  have e1 : H.map (regO y z).subtype = h * b := by ext; rfl
  have e2 : H'.map (regO y z).subtype = (h * b)⁻¹ := by ext; rfl
  refine ⟨b, H, H', hb, hbt, hbd, fun a c e => Subtype.ext ((hhb.mul hb) a c e), ?_, ?_⟩
  · refine Matrix.map_injective (f := (regO y z).subtype) Subtype.val_injective ?_
    show (H' * H).map _ = (1 : Matrix (Fin N) (Fin N) (regO y z)).map _
    rw [Matrix.map_mul, e1, e2, Matrix.nonsing_inv_mul _ hd.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [e1, ← Matrix.mul_assoc, hTh]

end PositivityTheory.Xgp.W

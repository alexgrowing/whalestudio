import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsFlagFrame
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem map_sum_minor {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : Finset (Fin N) → R)
    (H : Matrix (Fin N) (Fin N) R) (J : Finset (Fin N)) :
    f (∑ I, u I * minorIJ H I J) = ∑ I, f (u I) * minorIJ (H.map f) I J := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [map_mul, CPts.minorIJ_map]

theorem frame_colsB {τ : Ψ} {a b ca cb : Fin N} {k₀ : K} (s : Swp N j a b ca cb) (hk : M.blk (τ, a) = some k₀)
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {H bb : Matrix (Fin N) (Fin N) Φ} (hH : IsBlockDiag j H)
    (hbb : IsBlockDiag j bb) (hbt : bb.BlockTriangular id)
    (e : (F.T τ).map (algebraMap M.Ω Φ) * H = M.g τ * bb) (m : ι k₀) :
    algebraMap M.Ω Φ (detFac j a (F.T τ)) * ((∏ c ∈ (stepCols N j a).erase ca, bb c c) *
      (bb cb cb * vecB M τ a k₀ ca cb m + bb ca cb * y ⟨k₀, m⟩)) =
      algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, a) k') *
        ∑ I, algebraMap M.Ω Φ (F.u ⟨k₀, m⟩ I) * minorIJ H I (colsB N j a ca cb) := by
  haveI : Infinite M.Ω := Infinite.of_injective (Nat.cast : ℕ → M.Ω) Nat.cast_injective
  have h1 := GlobalTheory.T.minor_sum_identity_base_change M.Ω N j (F.T τ) _ _ (M.coef ⟨k₀, m⟩) (F.u ⟨k₀, m⟩) (stepCols N j a)
    (hF.2.1 (τ, a) k₀ hk m) Φ _ (s.block_swap hH)
  have e2 : (F.T τ).map (algebraMap M.Ω Φ) * H.updateCol ca (fun r => H r cb) =
      (M.g τ * bb).updateCol ca fun r => (M.g τ * bb) r cb := by
    rw [← e]
    ext r c
    simp only [Matrix.mul_apply, updateCol_apply]
    split_ifs <;> rfl
  simp only [e2, ← s.minor_colsB, s.minor_colsB_mul _ hbb hbt] at h1
  rw [← h1, vecB, M.y_step (τ, a) k₀ hk m]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun I _ => by ring

theorem core {τ : Ψ} {a b ca cb : Fin N} {k₀ : K} (s : Swp N j a b ca cb) (hk : M.blk (τ, a) = some k₀)
    {z : (Σ k, ι k) → L} (hz : IsPt y z) (c : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0)
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    (uv : (Σ k, ι k) → Finset (Fin N) → L) (huv : ∀ q I, HasVal M.x (basePart M.blk z) (F.u q I) (uv q I))
    (υv : Fin N → L) (hυ : ∀ i, M.blk (τ, i) = none → HasVal M.x (basePart M.blk z) (F.υ (τ, i)) (υv i)) :
    ∃ (PF : PenFrame y k₀ (vecB M τ a k₀ ca cb) (cFac M τ a) (eDeg M τ a k₀) z c) (H₀ : Matrix (Fin N) (Fin N) L)
      (ev : Fin N → L), IsBlockDiag j H₀ ∧ H₀.det ≠ 0 ∧
      (∀ i k, M.blk (τ, i) = some k → ev i ≠ 0 ∧
        ∀ m, ev i * z ⟨k, m⟩ = ∑ I, uv ⟨k, m⟩ I * minorIJ H₀ I (stepCols N j i)) ∧
      (∀ m, PF.pv m = ∑ I, uv ⟨k₀, m⟩ I * minorIJ H₀ I (stepCols N j a)) ∧
      (∀ m, PF.rv m = ∑ I, uv ⟨k₀, m⟩ I * minorIJ H₀ I (colsB N j a ca cb)) ∧
      PF.sv = muI N j b H₀ * PF.pv (c k₀) ^ 2 * ∏ i, ((if IsProperStep N j i then ev i else υv i) *
        (∏ k', basePart M.blk z ⟨k', F.c k'⟩ ^ M.b (τ, i) k') * chartMono z c (M.dy (τ, i))) ^ xiCoef τ a (τ, i) := by
  obtain ⟨bb, H, H', hbb, hbt, hbd, hH, hH', e⟩ := exists_flag_frame M τ hz hF hG
  let am := algebraMap M.Ω Φ
  let O := regO y z
  let val := valO hz
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hz.coord_ne (hc k)
  let u : (Σ k, ι k) → Finset (Fin N) → O := fun q I => ⟨am (F.u q I), _, hasVal_base M (huv q I)⟩
  let u' : Finset (Fin N) → (Σ k, ι k) → O := fun I q => ⟨am (F.u' I q),
    (exists_hasVal_of_regAt (hG.2.1 q I).2).imp fun _ => hasVal_base M⟩
  have hu : ∀ q I, val (u q I) = uv q I := fun q I => valO_eq hz _ (hasVal_base M (huv q I))
  have horth : ∀ i k, M.blk (τ, i) = some k → ∀ I I', IsStepRows N j i I → IsStepRows N j i I' →
      ∑ m, u' I ⟨k, m⟩ * u ⟨k, m⟩ I' = if I = I' then 1 else 0 := fun i k hp I I' h1 h2 => Subtype.ext (by
    have := congrArg am (hF.2.2.1 (τ, i) k hp I I' h1 h2)
    rw [map_sum] at this
    simp only [map_mul] at this
    simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
    refine this.trans ?_
    split_ifs <;> simp)
  let wf : (Σ k, ι k) → Finset (Fin N) → O := fun q J => ∑ I, u q I * minorIJ H I J
  let du : Fin N → Finset (Fin N) → (Σ k, ι k) → O := fun i J q =>
    ∑ I, (if IsStepRows N j i I then minorIJ H' J I else 0) * u' I q
  have hwf : ∀ q J, (wf q J : Φ) = ∑ I, am (F.u q I) * minorIJ (H.map O.subtype) I J := fun q J =>
    map_sum_minor O.subtype _ _ _
  have hwv : ∀ q J, val (wf q J) = ∑ I, uv q I * minorIJ (H.map val) I J := fun q J => by
    rw [map_sum_minor]; simp only [hu]
  have hdu : ∀ i k, M.blk (τ, i) = some k → ∀ J J', (∀ I, ¬ IsStepRows N j i I → minorIJ H I J = 0) →
      ∑ m, du i J' ⟨k, m⟩ * wf ⟨k, m⟩ J = minorIJ 1 J' J := fun i k hp J J' h0 => by
    rw [← hH']
    exact dual_sum' i (fun m I => u ⟨k, m⟩ I) (fun I m => u' I ⟨k, m⟩) (horth i k hp) H H' J J' h0
  have hD : ∀ i, am (detFac j i (F.T τ)) ≠ 0 := fun i =>
    (map_ne_zero am).2 (CPts.detFac_ne_zero M.j_le i (hF.1 τ).1 (hF.1 τ).2)
  let xF : Fin N → Φ := fun i => am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k')
  have hE : ∀ i, xF i ≠ 0 := fun i => (map_ne_zero am).2
    (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (M.x_chart_ne (isPt_base M hz).le hG k'))
  have rel : ∀ i k, M.blk (τ, i) = some k → ∀ m, am (detFac j i (F.T τ)) * (∏ c ∈ stepCols N j i, bb c c) * y ⟨k, m⟩ =
      xF i * wf ⟨k, m⟩ (stepCols N j i) := fun i k hp m => by
    rw [hwf]
    exact CPts.frame_gen M hF (RingHom.id Φ) hp m (hH.map _) hbb hbt e
  have hev : ∀ i, ∃ ev : L, ∀ k, M.blk (τ, i) = some k → ev ≠ 0 ∧
      ∀ m, ev * z ⟨k, m⟩ = val (wf ⟨k, m⟩ (stepCols N j i)) := fun i => by
    cases hp : M.blk (τ, i) with
    | none => exact ⟨0, fun k h => by cases h⟩
    | some k =>
      have h1 : ∀ m, val (wf ⟨k, c k⟩ (stepCols N j i)) / z ⟨k, c k⟩ * z ⟨k, m⟩ =
          val (wf ⟨k, m⟩ (stepCols N j i)) := fun m => by
        have h2 := (hasVal_ratio hz m (c k) (hc k)).mul (hasVal_valO hz (wf ⟨k, c k⟩ (stepCols N j i)))
        have h3 : y ⟨k, m⟩ / y ⟨k, c k⟩ * wf ⟨k, c k⟩ (stepCols N j i) = wf ⟨k, m⟩ (stepCols N j i) := by
          refine mul_left_cancel₀ (hE i) ?_
          have := hyc k
          rw [mul_left_comm, ← rel i k hp, ← rel i k hp]
          field_simp
        rw [h3] at h2
        rw [show val (wf ⟨k, m⟩ (stepCols N j i)) = _ from valO_eq hz _ h2]
        ring
      refine ⟨val (wf ⟨k, c k⟩ (stepCols N j i)) / z ⟨k, c k⟩, fun k' h => ?_⟩
      obtain rfl := Option.some.inj h
      refine ⟨fun h0 => ?_, h1⟩
      have h4 := congrArg val (hdu i k hp _ (stepCols N j i) fun I hI => minor_stepCols_eq_zero M.j_le H I hH hI)
      rw [CPts.minorIJ_one, map_one, map_sum] at h4
      refine zero_ne_one (Eq.trans (Finset.sum_eq_zero fun m _ => ?_).symm h4)
      rw [map_mul, ← h1 m, h0, zero_mul, mul_zero]
  choose ev hev using hev
  let lam : Fin N → Φ := fun i => am (M.lam (τ, i))
  let Tm := (F.T τ).map am
  let Nv : Fin N → L := fun i => (if IsProperStep N j i then ev i else υv i) *
    (∏ k', basePart M.blk z ⟨k', F.c k'⟩ ^ M.b (τ, i) k') * chartMono z c (M.dy (τ, i))
  have hN : ∀ i, HasVal y z (nI N j lam Tm bb i * chartMono y c (M.dy (τ, i))) (Nv i) ∧ Nv i ≠ 0 := fun i => by
    have hzF : (∏ k', basePart M.blk z ⟨k', F.c k'⟩ ^ M.b (τ, i) k') ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (chart_ne M hG k')
    have hR : HasVal y z (xF i * ∏ k : NonPluckerBlocks M.blk, (y ⟨k.1, c k.1⟩ ^ M.b (τ, i) k)⁻¹)
        ((∏ k', basePart M.blk z ⟨k', F.c k'⟩ ^ M.b (τ, i) k') *
          ∏ k : NonPluckerBlocks M.blk, (z ⟨k.1, c k.1⟩ ^ M.b (τ, i) k)⁻¹) := by
      simp only [xF, map_prod, map_zpow₀, ← Finset.prod_mul_distrib]
      refine HasVal.prod _ fun k _ => ?_
      have := (hasVal_ratio hz (F.c k) (c k.1) (hc k.1)).zpow hz (div_ne_zero (chart_ne M hG k) (hc k.1)) (M.b (τ, i) k)
      rw [div_zpow, div_zpow, div_eq_mul_inv, div_eq_mul_inv] at this
      rw [← M.y_base ⟨k, F.c k⟩]
      exact this
    simp only [Nv, nI, chartMono_dy, Tm, detFac_map]
    by_cases hp : IsProperStep N j i
    · obtain ⟨k, hk⟩ := blk_some M τ hp
      rw [if_pos hp, if_pos hp, hk]
      simp only [Option.elim]
      refine ⟨?_, mul_ne_zero (mul_ne_zero (hev i k hk).1 hzF) (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k' _ =>
        inv_ne_zero (zpow_ne_zero _ (hc _))) (hc k))⟩
      have := (hasVal_valO hz (wf ⟨k, c k⟩ (stepCols N j i))).mul hR
      convert this using 1
      · linear_combination (∏ k : NonPluckerBlocks M.blk, (y ⟨k.1, c k.1⟩ ^ M.b (τ, i) k)⁻¹) * rel i k hk (c k)
      · rw [show valO hz (wf ⟨k, c k⟩ (stepCols N j i)) = _ from ((hev i k hk).2 (c k)).symm]; ring
    · have hk : M.blk (τ, i) = none := (M.blk_none _).2 hp
      have hυ0 : υv i ≠ 0 := fun h0 => by
        obtain ⟨w, hw⟩ := exists_hasVal_of_regAt (hG.2.2 _ hk).2.2
        have := (hυ i hk).mul hw
        rw [mul_inv_cancel₀ (hG.2.2 _ hk).1, h0, zero_mul] at this
        exact zero_ne_one (this.unique (isPt_base M hz) hasVal_one)
      rw [if_neg hp, if_neg hp, hk]
      simp only [Option.elim]
      refine ⟨?_, mul_ne_zero (mul_ne_zero hυ0 hzF) (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k' _ =>
        inv_ne_zero (zpow_ne_zero _ (hc _))) one_ne_zero)⟩
      have := (hasVal_base M (hυ i hk)).mul hR
      have h5 := congrArg am (hF.2.2.2 (τ, i) hk)
      rw [map_mul, map_mul] at h5
      convert this using 1
      · linear_combination (∏ k : NonPluckerBlocks M.blk, (y ⟨k.1, c k.1⟩ ^ M.b (τ, i) k)⁻¹) * h5
      · ring
  let S := stepCols N j a
  let S' := colsB N j a ca cb
  let P := ∏ c ∈ S.erase ca, bb c c
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hbd c
  have hPa : ∏ c ∈ S, bb c c = bb ca ca * P := (Finset.mul_prod_erase _ _ s.ca_mem).symm
  have h0 : ∀ I, ¬ IsStepRows N j a I → minorIJ H I S = 0 := fun I hI => minor_stepCols_eq_zero M.j_le H I hH hI
  have h0' : ∀ I, ¬ IsStepRows N j a I → minorIJ H I S' = 0 := fun I hI => s.minor_colsB_eq_zero hH I hI
  have coe : ∀ {J J' : Finset (Fin N)} {t : O}, ∑ m, du a J' ⟨k₀, m⟩ * wf ⟨k₀, m⟩ J = t →
      ∑ m, (du a J' ⟨k₀, m⟩ : Φ) * wf ⟨k₀, m⟩ J = t := fun h => by
    rw [← h]; simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
  let ε := am (detFac j a (F.T τ)) * (bb ca ca * P) / xF a
  let γ := am (detFac j a (F.T τ)) * (P * bb cb cb) / xF a
  have hp : ∀ m, (wf ⟨k₀, m⟩ S : Φ) = ε * y ⟨k₀, m⟩ := fun m => by
    have := rel a k₀ hk m
    rw [hPa] at this
    rw [div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ (hE a)]
  have hmu : HasVal y z (muI N j b (H.map O.subtype)) (muI N j b (H.map val)) := by
    rw [muI_map, muI_map]; exact hasVal_valO hz _
  have hmu0 : muI N j b (H.map val) ≠ 0 := by
    have := congrArg val (muI_unit M.j_le b hH hH')
    rw [map_mul, map_one] at this
    rw [muI_map]
    exact right_ne_zero_of_mul_eq_one this
  have hpv0 : val (wf ⟨k₀, c k₀⟩ S) ≠ 0 := by
    rw [← (hev a k₀ hk).2]; exact mul_ne_zero (hev a k₀ hk).1 (hc k₀)
  have hsv : HasVal y z (cFac M τ a * ε * γ / chartMono y c (eDeg M τ a k₀))
      (muI N j b (H.map val) * val (wf ⟨k₀, c k₀⟩ S) ^ 2 * ∏ i, Nv i ^ xiCoef τ a (τ, i)) := by
    have h1 := (hmu.mul ((hasVal_valO hz (wf ⟨k₀, c k₀⟩ S)).pow 2)).mul
      (HasVal.prod Finset.univ fun i _ => (hN i).1.zpow hz (hN i).2 (xiCoef τ a (τ, i)))
    convert h1 using 1
    have hTd : Tm.det ≠ 0 := by
      rw [show Tm.det = am (F.T τ).det from (RingHom.map_det am _).symm]
      exact (map_ne_zero am).2 (hF.1 τ).2
    have h2 := s.alg τ lam ((hF.1 τ).1.map am) hTd (hH.map O.subtype) hbb hbt hbd e
    have h3 : cFac M τ a = ∏ i, facI N j a lam (M.g τ) i ^ xiCoef τ a (τ, i) := prod_xi_pair τ a _
    have h4 := chartMono_eDeg M hyc τ a k₀
    have h5 : γ * bb ca ca = ε * bb cb cb := by simp only [γ, ε]; ring
    rw [← h3] at h2
    simp only [mul_zpow, Finset.prod_mul_distrib]
    rw [hp, div_eq_iff (chartMono_ne hyc _)]
    refine mul_right_cancel₀ (hbd ca) ?_
    linear_combination (cFac M τ a * ε) * h5 + ε ^ 2 * h2 -
      (ε ^ 2 * muI N j b (H.map O.subtype) * bb ca ca * ∏ i, nI N j lam Tm bb i ^ xiCoef τ a (τ, i)) * h4
  have hcaS' : ca ∉ S' := by
    simp only [S', colsB, Finset.mem_insert, Finset.notMem_erase, or_false]; exact s.lt_cb.ne
  refine ⟨{
      p := fun m => wf ⟨k₀, m⟩ S, r := fun m => wf ⟨k₀, m⟩ S', α := fun m => du a S ⟨k₀, m⟩,
      β := fun m => du a S' ⟨k₀, m⟩, pv := fun m => val (wf ⟨k₀, m⟩ S), rv := fun m => val (wf ⟨k₀, m⟩ S'),
      αv := fun m => val (du a S ⟨k₀, m⟩), βv := fun m => val (du a S' ⟨k₀, m⟩), ε := ε, γ := γ,
      δ := am (detFac j a (F.T τ)) * (P * bb ca cb) / xF a, sv := _,
      hp := fun m => hasVal_valO hz _, hr := fun m => hasVal_valO hz _, hα := fun m => hasVal_valO hz _,
      hβ := fun m => hasVal_valO hz _,
      ε_ne := div_ne_zero (mul_ne_zero (hD a) (mul_ne_zero (hbd _) hP)) (hE a),
      γ_ne := div_ne_zero (mul_ne_zero (hD a) (mul_ne_zero hP (hbd _))) (hE a),
      p_eq := hp, r_eq := fun m => ?_,
      αp := coe (t := 1) ((hdu a k₀ hk S S h0).trans (CPts.minorIJ_one _)),
      αr := coe (t := 0) ((hdu a k₀ hk S' S h0').trans (minor_one_of_ne s.ca_mem hcaS')),
      βp := coe (t := 0) ((hdu a k₀ hk S S' h0).trans (minor_one_of_ne (Finset.mem_insert_self _ _) s.cb_notMem)),
      βr := coe (t := 1) ((hdu a k₀ hk S' S' h0').trans (CPts.minorIJ_one _)),
      hs := hsv,
      sv_ne := mul_ne_zero (mul_ne_zero hmu0 (pow_ne_zero _ hpv0))
        (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hN i).2) },
    H.map val, ev, hH.map _, ?_, fun i k hp => ⟨(hev i k hp).1, fun m => ((hev i k hp).2 m).trans (hwv _ _)⟩,
    fun m => hwv _ _, fun m => hwv _ _, rfl⟩
  · have := frame_colsB M s hk hF (hH.map O.subtype) hbb hbt e m
    refine mul_left_cancel₀ (hE a) ?_
    rw [hwf]
    refine this.symm.trans ?_
    have := hE a
    simp only [γ]
    field_simp
    ring
  · have := congrArg (fun A => val (Matrix.det A)) hH'
    simp only [det_mul, map_mul, det_one, map_one] at this
    rw [show (H.map val).det = val H.det from (RingHom.map_det val _).symm]
    exact right_ne_zero_of_mul_eq_one this

end PositivityTheory.Xgp.W

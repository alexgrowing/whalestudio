import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocalRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantShift
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace Mono

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isOpen_relevant : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem continuousAt_h {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContinuousAt A.h z :=
  hA.continuousOn.continuousAt (isOpen_relevant.mem_nhds hz)

theorem continuous_evalC (g : MRing ι) :
    Continuous fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) g) :=
  MvPolynomial.continuous_eval _

theorem eval_eq_of_aeval_eq {y : (Σ k, ι k) → Ω} {d : K → ℕ} {g g' : MRing ι}
    (hg : IsMultiHomog g d) (hg' : IsMultiHomog g' d) (he : aeval y g = aeval y g')
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) g) = eval z (map (Int.castRingHom ℂ) g') := by
  have hmem : g - g' ∈ mCoordIdeal y := by
    show mConeMap y (g - g') = 0
    rw [map_sub, ProjLine.mConeMap_eq_of_isMultiHomog y hg, ProjLine.mConeMap_eq_of_isMultiHomog y hg', he,
      sub_self]
  have h0 := hz.2 _ hmem
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

theorem bound_of_ptBoundOn (hLR : LocalRep.Statement) {y : (Σ k, ι k) → Ω} {M L : HermLine ι} {n : ℕ}
    {U : Set ((Σ k, ι k) → ℂ)} {c : ℝ} {f f' : Ω}
    (hL : IsSmoothHerm L) (hf : f ∈ chartLat y M.a n) (hf' : f' ∈ chartLat y L.a n)
    (hsm : IsSmallH (mCoordIdeal y) y M n f)
    (hU : mcPts (mCoordIdeal y) ⊆ closure (U ∩ mcPts (mCoordIdeal y)))
    (hb : PtBoundOn y M L n (U ∩ mcPts (mCoordIdeal y)) c f f') (hc : 0 ≤ c) :
    ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
      IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * L.a k) →
      aeval y g = f' * aeval y h → z ∈ mcPts (mCoordIdeal y) →
      ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * (‖eval z (map (Int.castRingHom ℂ) h)‖ * L.h z ^ n) := by
  intro dg dh g h z hg hh hd he hz
  obtain ⟨dg0, dh0, g0, h0, hg0, hh0, hd0, he0, hz0⟩ := hLR K ι Ω y M.a n f z hf hz
  obtain ⟨dg1, dh1, g1, h1, hg1, hh1, hd1, he1, hz1⟩ := hLR K ι Ω y L.a n f' z hf' hz
  have hLz : 0 < L.h z := L.pos z hz.1

  have step1 : ‖eval z (map (Int.castRingHom ℂ) g1)‖ /
      (‖eval z (map (Int.castRingHom ℂ) h1)‖ * L.h z ^ n) ≤ c := by
    have hVn : ({w | eval w (map (Int.castRingHom ℂ) h0) ≠ 0} ∩ {w | eval w (map (Int.castRingHom ℂ) h1) ≠ 0}) ∩
        {w : (Σ k, ι k) → ℂ | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} ∈ 𝓝 z :=
      (((isOpen_ne_fun (continuous_evalC h0) continuous_const).inter
        (isOpen_ne_fun (continuous_evalC h1) continuous_const)).inter isOpen_relevant).mem_nhds
        ⟨⟨hz0, hz1⟩, hz.1⟩
    set S : Set ((Σ k, ι k) → ℂ) := (({w | eval w (map (Int.castRingHom ℂ) h0) ≠ 0} ∩
        {w | eval w (map (Int.castRingHom ℂ) h1) ≠ 0}) ∩ {w : (Σ k, ι k) → ℂ | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0}) ∩
        (U ∩ mcPts (mCoordIdeal y)) with hS
    have hcl : z ∈ closure S := by
      rw [mem_closure_iff_nhds]
      intro t ht
      obtain ⟨w, ⟨hwt, hwV⟩, hwU⟩ := mem_closure_iff_nhds.mp (hU hz) _ (Filter.inter_mem ht hVn)
      exact ⟨w, hwt, hwV, hwU⟩
    have : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hcont : ContinuousAt (fun w => ‖eval w (map (Int.castRingHom ℂ) g1)‖ /
        (‖eval w (map (Int.castRingHom ℂ) h1)‖ * L.h w ^ n)) z := by
      refine ContinuousAt.div (continuous_evalC g1).norm.continuousAt
        (ContinuousAt.mul (continuous_evalC h1).norm.continuousAt ((continuousAt_h hL hz.1).pow n)) ?_
      exact mul_ne_zero (norm_ne_zero_iff.mpr hz1) (pow_ne_zero _ hLz.ne')
    refine le_of_tendsto (x := 𝓝[S] z) (hcont.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    obtain ⟨⟨⟨hw0, hw1⟩, hwr⟩, hwU, hwP⟩ := hw
    have hb' := hb dg0 dh0 dg1 dh1 g0 h0 g1 h1 hg0 hh0 hd0 he0 hg1 hh1 hd1 he1 w ⟨hwU, hwP⟩ hw0 hw1
    have hs := hsm dg0 dh0 g0 h0 w hg0 hh0 hd0 he0 hwP
    have hden : 0 < ‖eval w (map (Int.castRingHom ℂ) h0)‖ * M.h w ^ n :=
      mul_pos (norm_pos_iff.mpr hw0) (pow_pos (M.pos w hwr) n)
    have hr : ‖eval w (map (Int.castRingHom ℂ) g0)‖ /
        (‖eval w (map (Int.castRingHom ℂ) h0)‖ * M.h w ^ n) ≤ 1 := (div_le_one hden).mpr hs
    calc _ ≤ _ := hb'
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hr hc
      _ = c := mul_one c
  have hpos1 : 0 < ‖eval z (map (Int.castRingHom ℂ) h1)‖ * L.h z ^ n :=
    mul_pos (norm_pos_iff.mpr hz1) (pow_pos hLz n)
  have hb1 : ‖eval z (map (Int.castRingHom ℂ) g1)‖ ≤ c * (‖eval z (map (Int.castRingHom ℂ) h1)‖ * L.h z ^ n) :=
    (div_le_iff₀ hpos1).mp step1

  have hdeg : dg + dh1 = dg1 + dh := by
    funext k
    have e1 := hd k
    have e2 := hd1 k
    have : ((dg k + dh1 k : ℕ) : ℤ) = ((dg1 k + dh k : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have hm1 : IsMultiHomog (g * h1) (dg + dh1) := isMultiHomog_mul' hg hh1
  have hm2 : IsMultiHomog (g1 * h) (dg + dh1) := by rw [hdeg]; exact isMultiHomog_mul' hg1 hh
  have hval : aeval y (g * h1) = aeval y (g1 * h) := by
    rw [map_mul, map_mul, he, he1]
    ring
  have hez := eval_eq_of_aeval_eq hm1 hm2 hval hz
  simp only [map_mul] at hez
  have hkey : ‖eval z (map (Int.castRingHom ℂ) g)‖ * ‖eval z (map (Int.castRingHom ℂ) h1)‖ ≤
      (c * (‖eval z (map (Int.castRingHom ℂ) h)‖ * L.h z ^ n)) * ‖eval z (map (Int.castRingHom ℂ) h1)‖ := by
    rw [← norm_mul, hez, norm_mul]
    calc ‖eval z (map (Int.castRingHom ℂ) g1)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ ≤
        c * (‖eval z (map (Int.castRingHom ℂ) h1)‖ * L.h z ^ n) * ‖eval z (map (Int.castRingHom ℂ) h)‖ :=
          mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
      _ = _ := by ring
  exact le_of_mul_le_mul_right hkey (norm_pos_iff.mpr hz1)

theorem smallSectionCount_le_of_injOn {P Q : ℕ → Ω → Prop} {La La' : ℕ → AddSubgroup Ω} {n : ℕ} (φ : Ω → Ω)
    (hinj : Set.InjOn φ (La n)) (hmaps : ∀ s ∈ La n, P n s → φ s ∈ La' n ∧ Q n (φ s))
    (hfin : {s : La' n | Q n (s : Ω)}.Finite) : smallSectionCount P La n ≤ smallSectionCount Q La' n := by
  unfold smallSectionCount
  have : Finite {s : La' n // Q n (s : Ω)} := hfin.to_subtype
  have hle : Nat.card {s : La n // P n (s : Ω)} ≤ Nat.card {s : La' n // Q n (s : Ω)} :=
    Nat.card_le_card_of_injective
      (fun s => ⟨⟨φ s.1, (hmaps s.1 s.1.2 s.2).1⟩, (hmaps s.1 s.1.2 s.2).2⟩)
      (fun s t hst => by
        have h1 : φ s.1 = φ t.1 := congrArg (fun u : {s : La' n // Q n (s : Ω)} => ((u.1 : La' n) : Ω)) hst
        exact Subtype.ext (Subtype.ext (hinj s.1.2 t.1.2 h1)))
  rcases Nat.eq_zero_or_pos (Nat.card {s : La n // P n (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

theorem card_eq_of_iff {La La' : AddSubgroup Ω} {Q Q' : Ω → Prop}
    (h : ∀ s, s ∈ La ∧ Q s ↔ s ∈ La' ∧ Q' s) :
    Nat.card {s : La // Q (s : Ω)} = Nat.card {s : La' // Q' (s : Ω)} :=
  Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ La) Q).trans
    ((Equiv.subtypeEquivRight h).trans (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ La') Q').symm))

theorem chartLat_hermZpow (y : (Σ k, ι k) → Ω) (M : HermLine ι) (a m : ℕ) :
    chartLat y (Inter.hermZpow M a).a m = chartLat y M.a (a * m) := by
  have e : ∀ k, -((m : ℤ) * (Inter.hermZpow M a).a k) = -(((a * m : ℕ) : ℤ) * M.a k) := by
    intro k
    simp only [Inter.hermZpow, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  ext s
  change (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * (Inter.hermZpow M a).a k)) ∈ chartRingZ y c) ↔
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-(((a * m : ℕ) : ℤ) * M.a k)) ∈ chartRingZ y c)
  simp only [e]

theorem isSmallH_hermZpow_iff (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (M : HermLine ι) (a m : ℕ)
    (s : Ω) : IsSmallH P y (Inter.hermZpow M a) m s ↔ IsSmallH P y M (a * m) s := by
  have h1 : ∀ k, (m : ℤ) * (Inter.hermZpow M a).a k = ((a * m : ℕ) : ℤ) * M.a k := by
    intro k
    simp only [Inter.hermZpow, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have h2 : ∀ z, (Inter.hermZpow M a).h z ^ m = M.h z ^ (a * m) := by
    intro z
    show (M.h z ^ (a : ℤ)) ^ m = _
    rw [zpow_natCast, pow_mul]
  unfold IsSmallH
  simp only [h1, h2]

theorem smallSectionCount_tensorPower (y : (Σ k, ι k) → Ω) (M : HermLine ι) (a m : ℕ) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y (Inter.hermZpow M a)) (chartLat y (Inter.hermZpow M a).a) m =
      smallSectionCount (IsSmallH (mCoordIdeal y) y M) (chartLat y M.a) (a * m) := by
  unfold smallSectionCount
  rw [card_eq_of_iff (fun s => by rw [chartLat_hermZpow, isSmallH_hermZpow_iff])]

theorem semipos_hermZpow {P0 P : Ideal (MRing ι)} {M : HermLine ι} (h : IsSemipositiveRel P0 P M) (a : ℕ) :
    IsSemipositiveRel P0 P (Inter.hermZpow M a) := by
  refine ⟨Inter.isSmoothHerm_hermZpow h.1 _, fun z hz w hw => ?_⟩
  have hf : (fun z => Real.log ((Inter.hermZpow M a).h z)) = (a : ℝ) • fun z => Real.log (M.h z) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    show Real.log (M.h z ^ (a : ℤ)) = (a : ℝ) * Real.log (M.h z)
    rw [zpow_natCast, Real.log_pow]
  have h0 := h.2 z hz w hw
  unfold leviForm at h0 ⊢
  rw [hf, fderiv_const_smul_field]
  rw [fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ fun z => Real.log (M.h z)) (a : ℝ)]
  simp only [Pi.smul_apply, FunLike.coe_smul, smul_eq_mul]
  rw [← mul_add, mul_div_assoc]
  exact mul_nonneg (Nat.cast_nonneg a) h0

theorem geoNum_one_smul (W : Ideal (MRing ι)) (c : ℤ) (b : K → ℤ) :
    geoNum 1 W (fun _ => c • b) = c * geoNum 1 W (fun _ => b) := by
  rw [geoNum, geoNum]
  split_ifs with h
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : (Fin.init fun _ : Fin 1 => c • b) = Fin.init fun _ : Fin 1 => b := Subsingleton.elim _ _
    simp only [Pi.smul_apply, smul_eq_mul, e]
    ring
  · simp

theorem nef_hermZpow {P : Ideal (MRing ι)} {M : HermLine ι} (h : NefOnFibres P M.a) (a : ℕ) :
    NefOnFibres P (Inter.hermZpow M a).a := by
  intro W h1 h2 h3 h4
  show 0 ≤ geoNum 1 W (fun _ => (a : ℤ) • M.a)
  rw [geoNum_one_smul]
  exact mul_nonneg (Nat.cast_nonneg _) (h W h1 h2 h3 h4)

theorem conj_hermZpow {M : HermLine ι} (h : IsConjInvariantH M) (a : ℕ) :
    IsConjInvariantH (Inter.hermZpow M a) := fun z => by
  show M.h _ ^ (a : ℤ) = M.h z ^ (a : ℤ)
  rw [h z]

theorem fam_hermZpow {I : Ideal (MRing ι) → (m : ℕ) → (Fin m → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) {M : HermLine ι} (hM : IsSmoothHerm M) (a : ℕ) :
    I P (D + 1) (fun _ => Inter.hermZpow M a) = (a : ℝ) ^ (D + 1) * I P (D + 1) (fun _ => M) := by
  have hZ := Inter.isSmoothHerm_hermZpow hM (a : ℤ)
  let Lj : ℕ → Fin (D + 1) → HermLine ι := fun j i => if (i : ℕ) < j then Inter.hermZpow M a else M
  have hs : ∀ j i, IsSmoothHerm (Lj j i) := fun j i => by
    simp only [Lj]
    split_ifs
    exacts [hZ, hM]
  have step : ∀ j, j < D + 1 → I P (D + 1) (Lj (j + 1)) = a * I P (D + 1) (Lj j) := by
    intro j hj
    have e1 : Lj (j + 1) = Function.update (Lj j) ⟨j, hj⟩ (Inter.hermZpow M a) := by
      funext i
      by_cases hi : i = ⟨j, hj⟩
      · subst hi
        simp [Lj]
      · rw [Function.update_of_ne hi]
        have hij : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
        simp only [Lj]
        by_cases h1 : (i : ℕ) < j
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    have e0 : Lj j = Function.update (Lj j) ⟨j, hj⟩ M := by
      funext i
      by_cases hi : i = ⟨j, hj⟩
      · subst hi
        simp [Lj]
      · rw [Function.update_of_ne hi]
    rw [e1, Inter.fam_update_eq_snoc hI hP (Lj j) (hs j) ⟨j, hj⟩ hZ]
    conv_rhs => rw [e0, Inter.fam_update_eq_snoc hI hP (Lj j) (hs j) ⟨j, hj⟩ hM]
    rw [Inter.fam_snoc_zpow hI hP _ (fun i => hs j _) hM (a : ℤ)]
    push_cast
    ring
  have hall : ∀ j, j ≤ D + 1 → I P (D + 1) (Lj j) = (a : ℝ) ^ j * I P (D + 1) (Lj 0) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [step j (by omega), ih (by omega), pow_succ]
      ring
  have h0 : Lj 0 = fun _ => M := by
    funext i
    simp [Lj]
  have hD : Lj (D + 1) = fun _ => Inter.hermZpow M a := by
    funext i
    simp [Lj, i.2]
  rw [← hD, hall (D + 1) le_rfl, h0]

theorem constShift_a (A : HermLine ι) (t : ℝ) : (HermLine.constShift A t).a = A.a := by
  show A.a + 0 = A.a
  exact add_zero _

theorem constShift_h (A : HermLine ι) (t : ℝ) (z : (Σ k, ι k) → ℂ) :
    (HermLine.constShift A t).h z = Real.exp (-t) * A.h z := by
  show A.h z * Real.exp (-t) = _
  ring

theorem semipos_constShift {P0 P : Ideal (MRing ι)} {A : HermLine ι} (h : IsSemipositiveRel P0 P A) (t : ℝ) :
    IsSemipositiveRel P0 P (HermLine.constShift A t) := by
  have hh : (HermLine.constShift A t).h = fun z => Real.exp (-t) * A.h z := funext (constShift_h A t)
  refine ⟨?_, fun z hz w hw => ?_⟩
  · unfold IsSmoothHerm
    rw [hh]
    exact contDiffOn_const.mul h.1
  · have hev : (fun z => Real.log ((HermLine.constShift A t).h z)) =ᶠ[𝓝 z]
        fun z => -t + Real.log (A.h z) := by
      filter_upwards [isOpen_relevant.mem_nhds hz.1] with z' hz'
      rw [constShift_h, Real.log_mul (Real.exp_pos _).ne' (A.pos z' hz').ne', Real.log_exp]
    have h2 : fderiv ℝ (fderiv ℝ fun z => Real.log ((HermLine.constShift A t).h z)) z =
        fderiv ℝ (fderiv ℝ fun z => Real.log (A.h z)) z := by
      rw [hev.fderiv.fderiv_eq]
      congr 1
      funext x
      exact fderiv_const_add _
    unfold leviForm
    rw [h2]
    exact h.2 z hz w hw

theorem conj_constShift {A : HermLine ι} (h : IsConjInvariantH A) (t : ℝ) :
    IsConjInvariantH (HermLine.constShift A t) := fun z => by
  rw [constShift_h, constShift_h, h z]

theorem smallGen_constShift {P0 : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {D : ℕ} {L : HermLine ι}
    (h : IsSmallGeneratedDatum P0 y D L) {t : ℝ} (ht : t ≤ 0) :
    IsSmallGeneratedDatum P0 y D (HermLine.constShift L t) := by
  obtain ⟨q, w, hw, hgen, hsmall⟩ := h.gen
  refine ⟨h.normalForm_baseLattice_le_dualSpan_sup_line, semipos_constShift h.semipos t, ?_, ⟨q, w, ?_, ?_, fun j => ?_⟩⟩
  · rw [constShift_a]
    exact h.deg_pos
  · rw [constShift_a]
    exact hw
  · rw [constShift_a]
    exact hgen
  · intro dg dh g hh z hg hhh hd he hz
    rw [constShift_a] at hd
    have h1 := hsmall j dg dh g hh z hg hhh hd he hz
    rw [constShift_h, pow_one]
    rw [pow_one] at h1
    have hL := (L.pos z hz.1).le
    have he1 : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    nlinarith

theorem chartLat_le_nm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h1 := hs c hc
  exact isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, h1⟩)

end Mono

open Mono in

theorem G3.proof (hLR : LocalRep.Statement) (hCS : ConstantShift.Statement) (h6 : ArithmeticVolumeBig.Statement)
    (h7 : G7.Statement) (hPack : PackingStatement) : G3.Statement := by
  intro K _ ι _ Ω _ _ y D M L' P0 P0' II a iota hD hII har hb hM hL hLc ha hio hbd
  have hsmL : IsSmoothHerm L' := hL.semipos.1
  have hsmM : IsSmoothHerm M := hM.semipos.1
  have hfam : IsIntersectionFamily (II K ι) := hII K ι
  have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hapos : (0 : ℝ) < (a : ℝ) ^ (D + 1) := pow_pos ha0 _
  have key : ∀ η : ℝ, 0 < η →
      II K ι (mCoordIdeal y) (D + 1) (fun _ => M) ≤
        II K ι (mCoordIdeal y) (D + 1) (fun _ => L') + ((D : ℝ) + 1) * η * geomDeg (mCoordIdeal y) L' D := by
    intro η hη
    have hLa : (HermLine.constShift L' (-η)).a = L'.a := constShift_a L' (-η)
    have hLh : ∀ z, (HermLine.constShift L' (-η)).h z = Real.exp η * L'.h z := fun z => by
      rw [constShift_h, neg_neg]
    have hLsm : IsSmoothHerm (HermLine.constShift L' (-η)) := (semipos_constShift hL.semipos (-η)).1
    obtain ⟨n₀, O, -, hOd, hOb⟩ := hbd η hη
    obtain ⟨hfin, C, hC⟩ := hPack K ι Ω y D (HermLine.constShift L' (-η))
      (chartLat y (HermLine.constShift L' (-η)).a) har hb hLsm
      (fun τ => chartLat_le_nm y (HermLine.constShift L' (-η)).a τ)
    have hG7 := h7 K ι Ω y D (HermLine.constShift L' (-η)) P0' II hD hII har hb
      (smallGen_constShift hL (by linarith)) (conj_constShift hLc (-η))
    have hG6 := h6 K ι Ω y D (Inter.hermZpow M a) P0 II hD hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line
      (semipos_hermZpow hM.semipos a) (nef_hermZpow hM.nef a) (conj_hermZpow hM.conjInv a)
    rw [fam_hermZpow hfam har hsmM a] at hG6
    have hCS' := hCS K ι (II K ι) (mCoordIdeal y) D L' (-η) hfam har hsmL

    set v : ℕ → ℝ := fun n => smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.constShift L' (-η)))
      (chartLat y (HermLine.constShift L' (-η)).a) n / ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) with hv
    have hv_bdd : ∀ n, v n ≤ |C| * ((D + 1).factorial : ℝ) * 2 ^ (D + 1) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hv]
        simp only [Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
          zero_pow, zero_div, div_zero]
        positivity
      · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hnpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
        rw [hv]
        dsimp only
        rw [div_le_iff₀ hnpos]
        have h1 := (hC n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
        have h2 : ((n : ℝ) + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
        calc _ ≤ |C| * ((n : ℝ) + 1) ^ (D + 1) := h1
          _ ≤ |C| * (2 * n) ^ (D + 1) := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
          _ = |C| * ((D + 1).factorial : ℝ) * 2 ^ (D + 1) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
            rw [mul_pow]
            field_simp
    have hvB : IsBoundedUnder (· ≤ ·) atTop v := isBoundedUnder_of ⟨_, hv_bdd⟩
    have hlimL : limsup v atTop ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift L' (-η)) := hG7

    have hcmp : ∀ n, n₀ ≤ n → a ∣ n →
        smallSectionCount (IsSmallH (mCoordIdeal y) y M) (chartLat y M.a) n ≤
          smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.constShift L' (-η)))
            (chartLat y (HermLine.constShift L' (-η)).a) n := by
      intro n hn hdvd
      obtain ⟨hinj, hmaps⟩ := hio n hdvd
      refine smallSectionCount_le_of_injOn (iota n) hinj (fun s hs hsm => ⟨?_, ?_⟩) (hfin n)
      · rw [hLa]
        exact hmaps hs
      · intro dg dh g h z hg hh hd he hz
        rw [hLa] at hd
        have hbd' := bound_of_ptBoundOn hLR hsmL hs (hmaps hs) hsm hOd (hOb n hn hdvd s hs)
          (Real.exp_pos _).le dg dh g h z hg hh hd he hz
        rw [hLh, mul_pow, ← Real.exp_nat_mul]
        calc _ ≤ _ := hbd'
          _ = _ := by ring

    have hchain : ∀ ε : ℝ, 0 < ε →
        (a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => M) ≤
          (a : ℝ) ^ (D + 1) * (limsup v atTop + ε) := by
      intro ε hε
      refine hG6.trans ?_
      unfold arVolP
      have hev1 : ∀ᶠ n in atTop, v n < limsup v atTop + ε :=
        eventually_lt_of_limsup_lt (by linarith) hvB
      have hten : Tendsto (fun m : ℕ => a * m) atTop atTop :=
        tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m ha) tendsto_id
      have hev2 : ∀ᶠ m in atTop, v (a * m) < limsup v atTop + ε := hten.eventually hev1
      refine limsup_le_of_le (isCoboundedUnder_le_of_le atTop (x := 0) fun m =>
        div_nonneg (Real.log_natCast_nonneg _) (by positivity)) ?_
      filter_upwards [hev2, eventually_ge_atTop (max n₀ 1)] with m hm hm1
      have hm1' : 1 ≤ m := le_of_max_le_right hm1
      have hmn : n₀ ≤ a * m := (le_of_max_le_left hm1).trans (Nat.le_mul_of_pos_left m ha)
      rw [one_mul, smallSectionCount_tensorPower]
      have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1'
      have hmpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
      have hc := hcmp (a * m) hmn (dvd_mul_right a m)
      calc _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.constShift L' (-η)))
            (chartLat y (HermLine.constShift L' (-η)).a) (a * m) / ((m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) :=
            div_le_div_of_nonneg_right hc hmpos.le
        _ = (a : ℝ) ^ (D + 1) * v (a * m) := by
            rw [hv]
            dsimp only
            push_cast
            field_simp
            ring
        _ ≤ (a : ℝ) ^ (D + 1) * (limsup v atTop + ε) := mul_le_mul_of_nonneg_left hm.le hapos.le
    have hM_le : II K ι (mCoordIdeal y) (D + 1) (fun _ => M) ≤ limsup v atTop :=
      le_of_forall_pos_le_add fun ε hε => le_of_mul_le_mul_left (hchain ε hε) hapos
    calc _ ≤ limsup v atTop := hM_le
      _ ≤ _ := hlimL
      _ = _ := by
        rw [hCS']
        ring

  refine le_of_forall_pos_le_add fun ε hε => ?_
  set G := geomDeg (mCoordIdeal y) L' D
  have hη0 : 0 < ε / (((D : ℝ) + 1) * (|G| + 1)) := by positivity
  refine (key _ hη0).trans ?_
  have h1 : ((D : ℝ) + 1) * (ε / (((D : ℝ) + 1) * (|G| + 1))) * G ≤
      ((D : ℝ) + 1) * (ε / (((D : ℝ) + 1) * (|G| + 1))) * (|G| + 1) :=
    mul_le_mul_of_nonneg_left ((le_abs_self G).trans (by linarith)) (by positivity)
  have h2 : ((D : ℝ) + 1) * (ε / (((D : ℝ) + 1) * (|G| + 1))) * (|G| + 1) = ε := by
    field_simp
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

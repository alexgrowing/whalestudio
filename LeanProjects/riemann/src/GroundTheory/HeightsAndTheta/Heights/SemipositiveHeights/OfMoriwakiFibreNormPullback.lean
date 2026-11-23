import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUpperNormalisation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMonomialShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSmallGenHeightsNonneg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootGridLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSeparation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNormalLocusRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjAvoidingForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRepresentatives
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormMax
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem zcomb_fsH_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) {a : K → ℕ} (ha : A.a = fun k => (a k : ℤ)) (q : ℕ) (k : K) :
    (HermLine.zcomb A (fsH ι) q 1).a k = ((q * a k + 1 : ℕ) : ℤ) := by
  simp only [HermLine.zcomb, fsH, HermLine.ofMetrics, ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.one_apply, mul_one]
  push_cast
  ring

theorem heightsNonneg_shift {P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {a : K → ℕ} (hA : IsSmoothHerm A) (ha : A.a = fun k => (a k : ℤ)) (hM : MonomialsBounded P A a) (q : ℕ)
    {η : ℝ} (hη : 0 ≤ η) (II : IntersectionSystem) (hII : IsIntersectionSystem II) :
    HeightsNonneg II P (HermLine.constShift (HermLine.zcomb A (fsH ι) q 1) (-η)) := by
  classical
  set B := HermLine.constShift (HermLine.zcomb A (fsH ι) q 1) (-η) with hB
  have hBa : ∀ k, B.a k = ((q * a k + 1 : ℕ) : ℤ) := fun k => by
    rw [hB, constShift_a]
    exact zcomb_fsH_a A ha q k
  let e := Fintype.equivFin (∀ k, ι k)
  let w : Fin (Fintype.card (∀ k, ι k)) → MRing ι := fun j => ∏ k, X ⟨k, e.symm j k⟩ ^ (q * a k + 1)
  refine SmallGenHeightsNonneg.proof K ι P B II _ w hII ?_ (fun k => by rw [hBa]; positivity) (fun j => ?_) (fun Q hQ _ => ?_)
    (fun j z hz => ?_)
  · exact isSmoothHerm_constShift (MonomialShift.isSmoothHerm_zcomb_fsH hA q) (-η)
  · have h := Conductor.homog_prod Finset.univ (fun k => (X ⟨k, e.symm j k⟩ : MRing ι) ^ (q * a k + 1))
      (fun k => (q * a k + 1) • Pi.single k 1)
      (fun k _ => SectionBounded.homog_pow (SectionBounded.homog_X ⟨k, e.symm j k⟩) _)
    convert h using 1
    funext k
    rw [hBa k, Int.toNat_natCast]
    simp [Finset.sum_apply, Pi.single_apply]
  · have : Q.IsPrime := hQ.1
    let c : ∀ k, ι k := fun k => (hQ.2.2 k).choose
    refine ⟨e c, fun hmem => ?_⟩
    simp only [w, Equiv.symm_apply_apply] at hmem
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact (hQ.2.2 k).choose_spec (this.mem_of_pow_mem _ hk)
  · have h1 := MonomialShift.norm_prod_le hM (e.symm j) q 1 hz
    have hpos : 0 ≤ A.h z ^ q * (fsH ι).h z ^ 1 :=
      mul_nonneg (pow_nonneg (A.pos z hz.1).le _) (pow_nonneg ((fsH ι).pos z hz.1).le _)
    have hBh : B.h z = A.h z ^ q * (fsH ι).h z ^ 1 * Real.exp η := by
      change A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) * Real.exp (-(-η)) = _
      rw [zpow_natCast, zpow_one, pow_one, neg_neg]
    simp only [w, map_prod, map_pow, map_X, eval_X]
    rw [hBh]
    exact h1.trans (le_mul_of_one_le_right hpos (Real.one_le_exp hη))

theorem upperNm_of_moriwaki (hM : MoriwakiHSStatement) (hPk : PackingStatement) {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ)
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem) (q : ℕ) (hD : 1 ≤ D)
    (hII : IsIntersectionSystem II) (har : IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y)
    (ha : A.a = fun k => (a k : ℤ)) (hP0 : P0 ≤ mCoordIdeal y) (hsemi : IsSemipositiveRel P0 (mCoordIdeal y) A)
    (hmon : MonomialsBounded (mCoordIdeal y) A a) (hconj : IsConjInvariantH A) (hq : 1 ≤ q) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1))
          (chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a) n ≤
        (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A (fsH ι) q 1) + ε) *
          ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
  set B := HermLine.zcomb A (fsH ι) q 1 with hBdef
  have : CharZero Ω := UpperNormalisation.charZero_of_isArithVar har
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  have hsg : IsSmallGeneratedDatum P0 y D B :=
    PerturbMonomial.full K ι Ω y D a A P0 q hD har hb ha hP0 hsemi hmon hq
  have hBconj : IsConjInvariantH B := isConjInvariantH_zcomb hconj isConjInvariantH_fsH _ _

  set b : K → ℕ := fun k => q * a k + 1 with hbdef
  have hBa' : B.a = fun k => (b k : ℤ) := funext fun k => zcomb_fsH_a A ha q k
  have hb1 : ∀ k, 1 ≤ b k := fun k => Nat.le_add_left 1 _

  obtain ⟨k0, c, hc, hc0, hcs⟩ :=
    Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond K ι Ω y b hb1 (UpperNormalisation.exists_coord_ne_zero har) hb
  obtain ⟨qg, w, hw, hgen, hwsm⟩ := hsg.gen
  have hcy : aeval y c ∈ chartLat y B.a k0 :=
    UpperNormalisation.secM_le_chartLat y B.a k0 (d := fun κ => k0 * b κ) (fun κ => by rw [hBa']; push_cast; ring)
      (Submodule.subset_span ⟨c, hc, rfl⟩)
  obtain ⟨Cc, hCc⟩ := SectionBounded.proof K ι Ω y B qg w hw hgen hwsm k0 (aeval y c) hcy

  set Ib := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hIb
  set G := geomDeg (mCoordIdeal y) B D with hG
  set η : ℝ := ε / (4 * (((D : ℝ) + 1) * (|G| + 1))) with hηdef
  have hη : 0 < η := by positivity
  set B' := HermLine.constShift B (-η) with hB'def
  have hB'a : B'.a = B.a := constShift_a B (-η)
  have hB'h : ∀ z, B'.h z = Real.exp η * B.h z := fun z => by
    show B.h z * Real.exp (-(-η)) = _
    rw [neg_neg, mul_comm]
  have hB'semi : IsSemipositiveRel P0 (mCoordIdeal y) B' := Mono.semipos_constShift hsg.semipos (-η)
  have hB'sm : IsSmoothHerm B' := hB'semi.1
  obtain ⟨hfin, -⟩ := hPk K ι Ω y D B' (chartLat y B'.a) har hb hB'sm (fun τ => Mono.chartLat_le_nm y B'.a τ)

  have hMor := hM K ι Ω y D B' P0 II hII har hb hP0 hB'semi (Mono.conj_constShift hBconj (-η))
    (ProjLine.nefOnFibres_of_nonneg _ _ fun k => by rw [hB'a, hBa']; positivity)
    (NefOnGenericOfSemipos.proof K ι _ P0 B' hP0 hB'semi)
    (heightsNonneg_shift hsemi.1 ha hmon q hη.le II hII)
  have hCS := ConstantShift.full K ι (II K ι) (mCoordIdeal y) D B (-η) (hII K ι) har hsg.semipos.1
  have hI' : II K ι (mCoordIdeal y) (D + 1) (fun _ => B') ≤ Ib + ε / 4 := by
    rw [hCS]
    have h1 : ((D : ℝ) + 1) * η * G ≤ ((D : ℝ) + 1) * η * (|G| + 1) :=
      mul_le_mul_of_nonneg_left ((le_abs_self G).trans (by linarith)) (by positivity)
    have h2 : ((D : ℝ) + 1) * η * (|G| + 1) = ε / 4 := by
      rw [hηdef]; field_simp
    linarith
  set v : ℕ → ℝ := fun n => smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) n /
    ((n : ℝ) ^ (D + 1) / F) with hv
  have hev1 : ∀ᶠ m in atTop, v m < Ib + ε / 2 :=
    hMor.eventually (gt_mem_nhds (by linarith))

  have hcmp : ∀ n : ℕ, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) →
      smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) := by
    intro n hCn
    refine Mono.smallSectionCount_le_of_injOn (Q := fun m => IsSmallH (mCoordIdeal y) y B' (m + k0))
      (La' := fun m => chartLat y B'.a (m + k0)) (fun s => aeval y c * s)
      (fun s _ t _ hst => mul_left_cancel₀ hc0 hst) (fun s hs hsm => ⟨?_, ?_⟩) (hfin (n + k0))
    · have hs' : s ∈ chartLatNm y (fun κ => (b κ : ℤ)) n := by rw [← hBa']; exact hs
      have := hcs n s hs'
      show aeval y c * s ∈ chartLat y B'.a (n + k0)
      rw [hB'a]
      exact UpperNormalisation.secM_le_chartLat y B.a (n + k0) (fun κ => by rw [hBa']; push_cast; ring) this
    · intro dg dh g h z hg hh hd he hz
      rw [hB'a] at hd
      have hch : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (c * h) ((fun κ => k0 * b κ) + dh) := SectionBounded.homog_mul hc hh
      have h1 := hsm dg ((fun κ => k0 * b κ) + dh) g (c * h) z hg hch
        (fun κ => by simp only [Pi.add_apply]; push_cast; rw [hd κ, hBa']; push_cast; ring)
        (by rw [he, map_mul]; ring) hz
      have h2 := hCc (fun κ => k0 * b κ) 0 c 1 z hc SectionBounded.homog_one
        (fun κ => by simp only [Pi.zero_apply]; rw [hBa']; push_cast; ring) (by rw [map_one, mul_one]) hz
      rw [map_one, map_one, norm_one, mul_one] at h2
      have hBz : 0 ≤ B.h z := (B.pos z hz.1).le
      rw [map_mul, eval_mul, norm_mul] at h1
      rw [hB'h, mul_pow, ← Real.exp_nat_mul, pow_add]
      have hhn : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := by positivity
      calc ‖eval z (map (Int.castRingHom ℂ) g)‖
          ≤ ‖eval z (map (Int.castRingHom ℂ) c)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := h1
        _ ≤ Cc * B.h z ^ k0 * ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := by
          rw [mul_assoc, mul_assoc (Cc * _)]
          exact mul_le_mul_of_nonneg_right h2 hhn
        _ ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) * B.h z ^ k0 * ‖eval z (map (Int.castRingHom ℂ) h)‖ *
            B.h z ^ n := by
          gcongr
        _ = _ := by
          rw [show ((n + k0 : ℕ) : ℝ) * η = η * ((n + k0 : ℕ) : ℝ) from mul_comm _ _]
          ring

  have hlim : Tendsto (fun n : ℕ => (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1)) atTop (𝓝 (Ib + ε / 2)) := by
    have h0 : Tendsto (fun n : ℕ => (k0 : ℝ) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul (Ib + ε / 2)
  have hev3 : ∀ᶠ n : ℕ in atTop, (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1) < Ib + ε :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ n : ℕ in atTop, v (n + k0) < Ib + ε / 2 :=
    (tendsto_add_atTop_nat k0).eventually hev1
  have hevC : ∀ᶠ n : ℕ in atTop, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (⌈|Cc| / η⌉₊)] with n hn
    have h1 : |Cc| / η ≤ ((n + k0 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈|Cc| / η⌉₊ ≤ n + k0 by omega))
    have h2 : |Cc| ≤ η * ((n + k0 : ℕ) : ℝ) := by rw [div_le_iff₀ hη] at h1; linarith
    have h3 := Real.add_one_le_exp (η * ((n + k0 : ℕ) : ℝ))
    linarith [le_abs_self Cc]
  filter_upwards [hev2, hev3, hevC, eventually_ge_atTop 1] with n h2 h3 hC hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmpos : (0 : ℝ) < ((n + k0 : ℕ) : ℝ) ^ (D + 1) / F := by
    have : (0 : ℝ) < ((n + k0 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + k0 by omega)
    positivity
  have hcount : smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) ≤
      (Ib + ε / 2) * (((n + k0 : ℕ) : ℝ) ^ (D + 1) / F) := by
    have := h2
    rw [hv] at this
    dsimp only at this
    rw [div_lt_iff₀ hmpos] at this
    exact this.le
  have hratio : ((n + k0 : ℕ) : ℝ) ^ (D + 1) = (1 + (k0 : ℝ) / n) ^ (D + 1) * (n : ℝ) ^ (D + 1) := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp
  calc smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n
      ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) := hcmp n hC
    _ ≤ (Ib + ε / 2) * (((n + k0 : ℕ) : ℝ) ^ (D + 1) / F) := hcount
    _ = ((Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1)) * ((n : ℝ) ^ (D + 1) / F) := by
      rw [hratio]; ring
    _ ≤ (Ib + ε) * ((n : ℝ) ^ (D + 1) / F) :=
      mul_le_mul_of_nonneg_right h3.le (by positivity)

theorem NefBundleMoriwaki.of_moriwaki (hM : MoriwakiHSStatement) (hPk : PackingStatement) : ArithmeticHilbertSamuelUpperBound := by
  intro K _ ι _ Ω _ y D a A P0 II hD hII hY hbir ha hP0 hsemi hmon hconj
  have hS := MonomialShift.proof hPk
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  let f : ℕ → ℝ := fun τ =>
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ / ((τ : ℝ) ^ (D + 1) / F)
  show limsup f atTop ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
  have hcnt : ∀ (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (La : ℕ → AddSubgroup Ω) (τ : ℕ),
      0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y B) La τ := fun B La τ => by
    unfold smallSectionCount
    exact Real.log_natCast_nonneg _
  have hf0 : ∀ τ, 0 ≤ f τ := fun τ => div_nonneg (hcnt _ _ _) (div_nonneg (by positivity) hFpos.le)

  have key : ∀ q : ℕ, 1 ≤ q → ∀ ε : ℝ, 0 < ε → limsup f atTop ≤
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A (fsH ι) q 1) + ε) / (q : ℝ) ^ (D + 1) := by
    intro q hq ε hε
    set B := HermLine.zcomb A (fsH ι) q 1 with hBdef
    set c := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) + ε with hc
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (upperNm_of_moriwaki hM hPk y D a A P0 II q hD hII hY hbir ha hP0 hsemi hmon hconj hq ε hε)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hbound : ∀ᶠ τ : ℕ in atTop, f τ ≤ c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1) := by
      filter_upwards [eventually_ge_atTop (q * N + 1)] with τ hτ
      have hτpos : (0 : ℝ) < τ := by exact_mod_cast (show 0 < τ by omega)
      have hmod := Nat.mod_lt τ (show 0 < q by omega)
      have hqn : τ ≤ q * (τ / q + 1) := by
        have := Nat.div_add_mod τ q
        rw [Nat.mul_add, mul_one]; omega
      have hnN : N ≤ τ / q + 1 := by
        have : N ≤ τ / q := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; omega)
        omega
      have hnq : (((τ / q + 1 : ℕ) : ℝ)) * q ≤ τ + q := by
        have := Nat.div_mul_le_self τ q
        have h' : (τ / q + 1) * q ≤ τ + q := by rw [Nat.add_mul, one_mul]; omega
        exact_mod_cast h'
      have h1 : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
          c * ((((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F) :=
        (hS K ι Ω y D a A P0 q τ (τ / q + 1) hY hbir ha hP0 hsemi hmon hq hqn).trans (hN _ hnN)
      have hc0 : 0 ≤ c := by
        have hpos : 0 < (((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F := by positivity
        exact (mul_nonneg_iff_of_pos_right hpos).mp ((hcnt _ _ _).trans h1)
      have hnle : (((τ / q + 1 : ℕ) : ℝ)) ≤ (τ + q) / q := by rw [le_div_iff₀ hqpos]; exact hnq
      have e : c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1) =
          c * ((((τ : ℝ) + q) / q) ^ (D + 1) / F) / ((τ : ℝ) ^ (D + 1) / F) := by
        rw [show (1 : ℝ) + q / τ = (τ + q) / τ by field_simp]
        simp only [div_pow]
        field_simp
      show smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ / ((τ : ℝ) ^ (D + 1) / F) ≤ _
      rw [e, div_le_div_iff_of_pos_right (by positivity)]
      calc _ ≤ c * ((((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F) := h1
        _ ≤ c * ((((τ : ℝ) + q) / q) ^ (D + 1) / F) := by gcongr
    have hlim : Tendsto (fun τ : ℕ => c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1)) atTop
        (𝓝 (c / (q : ℝ) ^ (D + 1))) := by
      have h0 : Tendsto (fun τ : ℕ => (q : ℝ) / τ) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul (c / (q : ℝ) ^ (D + 1))
    calc limsup f atTop ≤ limsup (fun τ : ℕ => c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1)) atTop :=
          limsup_le_limsup hbound (isCoboundedUnder_le_of_le atTop hf0) hlim.isBoundedUnder_le
      _ = c / (q : ℝ) ^ (D + 1) := hlim.limsup_eq

  have hT := tendsto_fam_zcomb (hII K ι) hY hsemi.1 (show IsSmoothHerm (fsH ι) from
    GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev : ∀ᶠ q : ℕ in atTop, limsup f atTop - ε ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A (fsH ι) q 1) / (q : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hk := key q hq ε hε
    have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (D + 1) := one_le_pow₀ (by exact_mod_cast hq)
    have hεq : ε / (q : ℝ) ^ (D + 1) ≤ ε := div_le_self hε.le hq1
    rw [add_div] at hk
    linarith
  have := ge_of_tendsto hT hev
  linarith

end

end GroundTheory.Heights₂.Heights.ForSecondHalf

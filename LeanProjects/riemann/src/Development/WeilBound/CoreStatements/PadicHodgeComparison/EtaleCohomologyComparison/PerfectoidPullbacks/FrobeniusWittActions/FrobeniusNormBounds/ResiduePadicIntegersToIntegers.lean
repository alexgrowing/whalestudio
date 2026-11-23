import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb.G3

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def padicIntegers_to_integers : ℤ_[l] →+* OK l K where
  toFun z := ⟨algebraMap ℚ_[l] K z, by
    change K.val (algebraMap ℚ_[l] K z) ∈ normInteger (PadicAlgCl l)
    rw [mem_normInteger, AlgHom.commutes, PadicAlgCl.norm_extends]
    exact z.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem padicIntegers_to_integers_coe (z : ℤ_[l]) : ((padicIntegers_to_integers (K := K) z : OK l K) : K) = algebraMap ℚ_[l] K z := rfl

theorem residue_padicIntegers_to_integers (r : Res l K) (z : ℤ_[l]) :
    r.ρ (padicIntegers_to_integers z) = (letI := ZMod.algebra r.k l; algebraMap (ZMod l) r.k (PadicInt.toZMod z)) := by
  let _ := ZMod.algebra r.k l
  have hs := PadicInt.toZMod_spec z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hs
  obtain ⟨w, hw⟩ := hs
  have e : z = (((PadicInt.toZMod z).val : ℕ) : ℤ_[l]) + w * l := by
    rw [hw, ZMod.cast_eq_val]; ring
  conv_lhs => rw [e]
  simp only [map_add, map_mul, map_natCast, CharP.cast_eq_zero r.k l, mul_zero, add_zero]
  rw [← map_natCast (algebraMap (ZMod l) r.k), ZMod.natCast_zmod_val]

theorem residue_field_card_le_finrank (r : Res l K) [FiniteDimensional ℚ_[l] K] (s : Finset r.k)
    (hs : letI := ZMod.algebra r.k l; LinearIndependent (ZMod l) (fun i : s => (i : r.k))) :
    s.card ≤ Module.finrank ℚ_[l] K := by
  classical
  let _ := ZMod.algebra r.k l
  let y : s → OK l K := fun i => (r.surj i).choose
  have hy : ∀ i, r.ρ (y i) = i := fun i => (r.surj i).choose_spec
  have hli : LinearIndependent ℚ_[l] (fun i : s => ((y i : OK l K) : K)) := by
    rw [linearIndependent_iff']
    intro t g hg i0 hi0
    by_contra hne
    obtain ⟨j, hj, hmax⟩ := t.exists_max_image (fun i => ‖g i‖) ⟨i0, hi0⟩
    have hgj : g j ≠ 0 := by
      intro h0
      apply hne
      have := hmax i0 hi0
      rw [h0, norm_zero] at this
      exact norm_le_zero_iff.1 this
    have hle : ∀ i ∈ t, ‖g i / g j‖ ≤ 1 := fun i hi => by
      rw [norm_div]
      exact div_le_one_of_le₀ (hmax i hi) (norm_nonneg _)
    let hZ : s → ℤ_[l] := fun i => if hi : i ∈ t then ⟨g i / g j, hle i hi⟩ else 0
    have hZv : ∀ i ∈ t, ((hZ i : ℤ_[l]) : ℚ_[l]) = g i / g j := fun i hi => by simp [hZ, hi]
    have hsumK : ∑ i ∈ t, ((padicIntegers_to_integers (K := K) (hZ i) * y i : OK l K) : K) = 0 := by
      have e : ∀ i ∈ t, ((padicIntegers_to_integers (K := K) (hZ i) * y i : OK l K) : K) = (g j)⁻¹ • (g i • ((y i : OK l K) : K)) := by
        intro i hi
        rw [Subring.coe_mul, padicIntegers_to_integers_coe, hZv i hi, smul_smul, Algebra.smul_def, div_eq_inv_mul]
      rw [Finset.sum_congr rfl e, ← Finset.smul_sum, hg, smul_zero]
    have hsum : ∑ i ∈ t, padicIntegers_to_integers (K := K) (hZ i) * y i = 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, hsumK]
      rfl
    have hk : ∑ i ∈ t, PadicInt.toZMod (hZ i) • (i : r.k) = 0 := by
      have := congrArg r.ρ hsum
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hy, residue_padicIntegers_to_integers, Algebra.smul_def]
    have h0 := (linearIndependent_iff'.1 hs) t _ hk j hj
    have h1 : hZ j = 1 := by
      apply Subtype.ext
      rw [hZv j hj, div_self hgj]
      rfl
    rw [h1, map_one] at h0
    exact one_ne_zero h0
  have := hli.fintype_card_le_finrank
  simpa using this

theorem res_frob (r : Res l K) [FiniteDimensional ℚ_[l] K] : ∃ f : ℕ, 0 < f ∧ ∀ z : r.k, z ^ l ^ f = z := by
  let _ := ZMod.algebra r.k l
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hr : Module.rank (ZMod l) r.k ≤ Module.finrank ℚ_[l] K := rank_le fun s hs => residue_field_card_le_finrank r s hs
  haveI : Module.Finite (ZMod l) r.k := Module.rank_lt_aleph0_iff.1 (hr.trans_lt Cardinal.natCast_lt_aleph0)
  haveI : Finite r.k := Module.finite_of_finite (ZMod l)
  letI := Fintype.ofFinite r.k
  obtain ⟨n, -, hn⟩ := FiniteField.card r.k l
  refine ⟨n, n.pos, fun z => ?_⟩
  rw [← hn]
  exact FiniteField.pow_card z

theorem norm_lt_one_of_residue_zero_alt (r : Res l K) (y : OK l K) (hy : r.ρ y = 0) : ‖((y : K) : PadicAlgCl l)‖ < 1 := by
  have h1 : ‖((y : K) : PadicAlgCl l)‖ ≤ 1 := mem_normInteger.1 y.2
  refine lt_of_le_of_ne h1 fun he => ?_
  have hz : ((y : K) : PadicAlgCl l) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at he; exact zero_ne_one he
  have hyK : (y : K) ≠ 0 := fun h => hz (by rw [h]; rfl)
  have hw : ((y : K)⁻¹ : K) ∈ OK l K := by
    show ‖(((y : K)⁻¹ : K) : PadicAlgCl l)‖ ≤ 1
    rw [IntermediateField.coe_inv, norm_inv, he, inv_one]
  have hmul : (y * ⟨_, hw⟩ : OK l K) = 1 := Subtype.ext (mul_inv_cancel₀ hyK)
  have := congrArg r.ρ hmul
  rw [map_mul, hy, zero_mul, map_one] at this
  exact zero_ne_one this

theorem norm_le_ramification_bound [FiniteDimensional ℚ_[l] K] (x : K) (hx : ‖(x : PadicAlgCl l)‖ < 1) :
    ‖(x : PadicAlgCl l)‖ ≤ (l : ℝ) ^ (-(1 : ℝ) / Module.finrank ℚ_[l] K) := by
  set z : PadicAlgCl l := (x : PadicAlgCl l) with hzdef
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  by_cases hz : z = 0
  · rw [hz, norm_zero]; exact Real.rpow_nonneg (by positivity) _
  have hint : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hmin : minpoly ℚ_[l] z = minpoly ℚ_[l] x := minpoly.algebraMap_eq (algebraMap K (PadicAlgCl l)).injective x
  have hdle : (minpoly ℚ_[l] z).natDegree ≤ Module.finrank ℚ_[l] K := hmin ▸ minpoly.natDegree_le x
  have hdpos : 0 < (minpoly ℚ_[l] z).natDegree := minpoly.natDegree_pos hint
  have ha0 : (minpoly ℚ_[l] z).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hz
  have hnorm : ‖z‖ = ‖(minpoly ℚ_[l] z).coeff 0‖ ^ (1 / ((minpoly ℚ_[l] z).natDegree : ℝ)) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (PadicAlgCl l) z
  set d := (minpoly ℚ_[l] z).natDegree
  set a := ‖(minpoly ℚ_[l] z).coeff 0‖
  have hd : (0 : ℝ) < d := by exact_mod_cast hdpos
  have ha0' : 0 ≤ a := norm_nonneg _
  have ha1 : a < 1 := by
    by_contra h
    push Not at h
    have : 1 ≤ a ^ (1 / (d : ℝ)) := Real.one_le_rpow h (by positivity)
    rw [← hnorm] at this
    exact absurd hx (not_lt.2 this)
  have hal : a ≤ (l : ℝ) ^ (-(1 : ℝ)) := by
    have hv := Padic.norm_eq_zpow_neg_valuation ha0
    change a = _ at hv
    rw [hv] at ha1 ⊢
    have hlt : -((minpoly ℚ_[l] z).coeff 0).valuation < 0 := by
      by_contra h; push Not at h
      exact absurd ha1 (not_lt.2 (one_le_zpow₀ hl1.le h))
    rw [Real.rpow_neg_one, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  rw [hnorm]
  calc a ^ (1 / (d : ℝ)) ≤ ((l : ℝ) ^ (-(1 : ℝ))) ^ (1 / (d : ℝ)) :=
        Real.rpow_le_rpow ha0' hal (by positivity)
    _ = (l : ℝ) ^ (-(1 : ℝ) / d) := by
        rw [← Real.rpow_mul (by positivity)]; ring_nf
    _ ≤ (l : ℝ) ^ (-(1 : ℝ) / Module.finrank ℚ_[l] K) := by
        apply Real.rpow_le_rpow_of_exponent_le hl1.le
        have hD : (d : ℝ) ≤ Module.finrank ℚ_[l] K := by exact_mod_cast hdle
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact one_div_le_one_div_of_le hd hD

theorem disc (r : Res l K) [FiniteDimensional ℚ_[l] K] :
    ∃ c : ℝ, c < 1 ∧ ∀ y : OK l K, r.ρ y = 0 → ‖((okToOC l K y : OC l) : ℂ_[l])‖ ≤ c := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hD : (0 : ℝ) < Module.finrank ℚ_[l] K := by exact_mod_cast Module.finrank_pos
  refine ⟨(l : ℝ) ^ (-(1 : ℝ) / Module.finrank ℚ_[l] K), Real.rpow_lt_one_of_one_lt_of_neg hl1 (by
    rw [neg_div]; exact neg_neg_of_pos (by positivity)), fun y hy => ?_⟩
  have e : ‖((okToOC l K y : OC l) : ℂ_[l])‖ = ‖((y : K) : PadicAlgCl l)‖ := norm_clToC _
  rw [e]
  exact norm_le_ramification_bound (y : K) (norm_lt_one_of_residue_zero_alt r y hy)

theorem norm_le_one_integer (x : OC l) : ‖((x : OC l) : ℂ_[l])‖ ≤ 1 := mem_normInteger.1 x.2

theorem norm_pow_sub_pow_le_bis (x y : OC l) :
    ‖((x ^ l - y ^ l : OC l) : ℂ_[l])‖ ≤ max (‖((x - y : OC l) : ℂ_[l])‖ ^ l) ‖(l : ℂ_[l])‖ := by
  obtain ⟨t, ht⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) y (x - y)
  rw [add_sub_cancel] at ht
  have e : x ^ l - y ^ l = (x - y) ^ l + (l : OC l) * y * (x - y) * t := by
    linear_combination ht
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · rw [show (((x - y) ^ l : OC l) : ℂ_[l]) = ((x - y : OC l) : ℂ_[l]) ^ l from rfl, norm_pow]
  · have h1 : (((l : OC l) * y * (x - y) * t : OC l) : ℂ_[l]) =
        (l : ℂ_[l]) * ((y : OC l) : ℂ_[l]) * ((x - y : OC l) : ℂ_[l]) * ((t : OC l) : ℂ_[l]) := by
      push_cast; rfl
    rw [h1, norm_mul, norm_mul, norm_mul]
    have := norm_le_one_integer y
    have := norm_le_one_integer (x - y)
    have := norm_le_one_integer t
    have h0 : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
    calc ‖(l : ℂ_[l])‖ * ‖((y : OC l) : ℂ_[l])‖ * ‖((x - y : OC l) : ℂ_[l])‖ * ‖((t : OC l) : ℂ_[l])‖
        ≤ ‖(l : ℂ_[l])‖ * 1 * 1 * 1 := by gcongr
      _ = ‖(l : ℂ_[l])‖ := by ring

theorem pow_close (a b : OC l) (c : ℝ) (h : ‖((a - b : OC l) : ℂ_[l])‖ ≤ c) (m : ℕ) :
    ‖((a ^ l ^ m - b ^ l ^ m : OC l) : ℂ_[l])‖ ≤ max ‖(l : ℂ_[l])‖ (c ^ l ^ m) := by
  have hc : 0 ≤ c := (norm_nonneg _).trans h
  have hl0 : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  have hl1 : ‖(l : ℂ_[l])‖ ≤ 1 := by
    have := norm_le_one_integer (l : OC l)
    simpa using this
  have lpos : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  induction m with
  | zero => simpa using le_max_of_le_right h
  | succ m ih =>
    have e1 : a ^ l ^ (m + 1) = (a ^ l ^ m) ^ l := by rw [pow_succ, pow_mul]
    have e2 : b ^ l ^ (m + 1) = (b ^ l ^ m) ^ l := by rw [pow_succ, pow_mul]
    rw [e1, e2]
    refine (norm_pow_sub_pow_le_bis _ _).trans (max_le ?_ (le_max_left _ _))
    have hd0 : 0 ≤ ‖((a ^ l ^ m - b ^ l ^ m : OC l) : ℂ_[l])‖ := norm_nonneg _
    calc ‖((a ^ l ^ m - b ^ l ^ m : OC l) : ℂ_[l])‖ ^ l ≤ (max ‖(l : ℂ_[l])‖ (c ^ l ^ m)) ^ l := by gcongr
      _ = max (‖(l : ℂ_[l])‖ ^ l) ((c ^ l ^ m) ^ l) := by
          rcases le_total ‖(l : ℂ_[l])‖ (c ^ l ^ m) with hh | hh
          · rw [max_eq_right hh, max_eq_right (pow_le_pow_left₀ hl0 hh l)]
          · rw [max_eq_left hh, max_eq_left (pow_le_pow_left₀ (pow_nonneg hc _) hh l)]
      _ ≤ max ‖(l : ℂ_[l])‖ (c ^ l ^ (m + 1)) := by
          rw [← pow_mul, ← pow_succ]
          exact max_le_max (pow_le_of_le_one hl0 hl1 (by omega)) le_rfl

theorem struct (r : Res l K) (n : ℕ) (x : OK l K) :
    Mid.κm r n x = B.uJ true (PAlg.base l) n ((PAlg.base l).oC (PreTilt.untilt (r.s (r.ρ x)))) := by
  have h1 : Wc.res l r.k n (r.ρ x) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (WittVector.teichmuller l (r.ρ x))) := by
    rw [← Wc.res_coeff]; simp
  have h2 : r.w (WittVector.teichmuller l (r.ρ x)) =
      algebraMap (Ainf l) (Acris l) (WittVector.teichmuller l (r.s (r.ρ x))) := by
    simp [Res.w, WittVector.map_teichmuller]
  have h3 : PreTilt.untilt (r.s (r.ρ x)) = theta0 l (WittVector.teichmuller l (r.s (r.ρ x))) :=
    (WittVector.fontaineTheta_teichmuller _).symm
  rw [h3, PAlg.oC_theta0, B.uJ_th, ← PAlg.cris_algebraMap, ← h2]
  simp only [Mid.κm, RingHom.comp_apply, h1]
  rfl

theorem cong (n : ℕ) (a b : OC l) (h : ‖((a - b : OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖) :
    B.uJ true (PAlg.base l) n ((PAlg.base l).oC a) = B.uJ true (PAlg.base l) n ((PAlg.base l).oC b) := by
  have hl : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl' : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 hl
  set d : ℂ_[l] := ((a - b : OC l) : ℂ_[l]) / (l : ℂ_[l]) with hd
  have hdm : d ∈ normInteger ℂ_[l] := by
    rw [mem_normInteger, hd, norm_div]
    exact (div_le_one hl').2 h
  have e : a = b + (l : OC l) * ⟨d, hdm⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, hd]
    rw [mul_div_cancel₀ _ hl]
    simp
  have z : (l : (B.bs l true n).R ⧸ (B.bs l true n).I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (B.bs l true n).I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  rw [e, map_add, map_add, map_mul, map_mul, map_natCast, map_natCast]
  change _ + (l : (B.bs l true n).R ⧸ (B.bs l true n).I) * _ = _
  rw [z, zero_mul, add_zero]

theorem exists_teichmuller_close (r : Res l K) [FiniteDimensional ℚ_[l] K] :
    ∃ c : ℝ, c < 1 ∧ ∀ x : OK l K, ‖((okToOC l K x - PreTilt.untilt (r.s (r.ρ x)) : OC l) : ℂ_[l])‖ ≤ c := by
  obtain ⟨f, hf, hfz⟩ := res_frob r
  obtain ⟨c, hc1, hc⟩ := disc r
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have : ‖(l : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := by
      rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l])]; exact norm_algebraMap' ℂ_[l] _
    rw [this]; exact Padic.norm_p_lt_one
  refine ⟨max c ‖(l : ℂ_[l])‖, max_lt hc1 hl1, fun x => ?_⟩
  set t : OC l := PreTilt.untilt (r.s (r.ρ x))
  set u : OC l := okToOC l K x - t
  have ht : t ^ l ^ f = t := by
    simp only [t]; rw [← map_pow, ← map_pow, hfz]
  have hker : r.ρ (x ^ l ^ f - x) = 0 := by rw [map_sub, map_pow, hfz, sub_self]
  have hq := hc _ hker
  by_contra hu
  push Not at hu
  have hu1 : ‖(u : ℂ_[l])‖ < 1 := by
    have := r.hs x
    simp only [u]
    push_cast at this ⊢
    rwa [norm_sub_rev] at this
  have hlu : ‖(l : ℂ_[l])‖ < ‖(u : ℂ_[l])‖ := (le_max_right _ _).trans_lt hu
  have hcu : c < ‖(u : ℂ_[l])‖ := (le_max_left _ _).trans_lt hu
  have hu0 : 0 < ‖(u : ℂ_[l])‖ := (norm_nonneg _).trans_lt hlu
  have hp := pow_close (okToOC l K x) t ‖(u : ℂ_[l])‖ le_rfl f
  rw [ht] at hp
  have hlf : 2 ≤ l ^ f := ((Fact.out : l.Prime).two_le).trans (Nat.le_self_pow hf.ne' l)
  have hpow : ‖(u : ℂ_[l])‖ ^ l ^ f < ‖(u : ℂ_[l])‖ := pow_lt_self_of_lt_one₀ hu0 hu1 (by omega)
  have hlt : ‖((okToOC l K x ^ l ^ f - t : OC l) : ℂ_[l])‖ < ‖(u : ℂ_[l])‖ := hp.trans_lt (max_lt hlu hpow)
  have e : ((okToOC l K (x ^ l ^ f - x) : OC l) : ℂ_[l]) = ((okToOC l K x ^ l ^ f - t : OC l) : ℂ_[l]) - (u : ℂ_[l]) := by
    simp only [u, map_sub, map_pow]; push_cast; ring
  rw [e] at hq
  have h3 := IsUltrametricDist.norm_add_le_max ((okToOC l K x ^ l ^ f - t : OC l) : ℂ_[l])
    (-(((okToOC l K x ^ l ^ f - t : OC l) : ℂ_[l]) - (u : ℂ_[l])))
  rw [← sub_eq_add_neg, sub_sub_cancel, norm_neg] at h3
  exact lt_irrefl _ (h3.trans_lt (max_lt hlt (hq.trans_lt hcu)))

theorem close (r : Res l K) [FiniteDimensional ℚ_[l] K] :
    ∃ N : ℕ, ∀ x : OK l K, ‖((okToOC l K x ^ l ^ N - PreTilt.untilt (r.s (r.ρ x)) : OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨f, hf, hfz⟩ := res_frob r
  obtain ⟨c, hc1, hc⟩ := exists_teichmuller_close r
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  have hl : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hl) hc1
  have hN : ∀ (M : ℕ) (z : r.k), z ^ l ^ (f * M) = z := by
    intro M z
    induction M with
    | zero => simp
    | succ M ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hfz]
  have hjN : j ≤ l ^ (f * j) :=
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le.trans (Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.le_mul_of_pos_left j hf))
  refine ⟨f * j, fun x => ?_⟩
  have ht : PreTilt.untilt (r.s (r.ρ x)) ^ l ^ (f * j) = PreTilt.untilt (r.s (r.ρ x)) := by
    rw [← map_pow, ← map_pow, hN]
  have hp := pow_close (okToOC l K x) (PreTilt.untilt (r.s (r.ρ x))) c (hc x) (f * j)
  rw [ht] at hp
  refine hp.trans (max_le le_rfl ?_)
  exact (pow_le_pow_of_le_one hc0 hc1.le hjN).trans hj.le

theorem teich (r : Res l K) [FiniteDimensional ℚ_[l] K] : ∃ N : ℕ, Mid.TeichmullerCongruence r N := by
  obtain ⟨N, hN⟩ := close r
  refine ⟨N, fun n x => ?_⟩
  rw [Mid.phiQ_pow, struct, ← cong n _ _ (hN x)]
  rw [map_pow, map_pow]
  rfl

end CrystallineSemistableComparison.Pb.G3

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatSFiniteSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdicSumExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TchNeMulOfPowEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem keyL : ∀ {l : ℕ} [Fact l.Prime] (b : Formalism.Per6.BdRp l) (k : ℕ),
    ∃ (c : ℕ) (a : Wl l), (l : Formalism.Per6.BdRp l) ^ c * b - wB l a ∈ FB l k := by
  intro l _ b k
  have hξ := GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[l] l
  set ξ := GroundTheory.PAdicHodge.IsPerfectoidField.kerThetaGenerator ℂ_[l] l with hξdef
  have hfg := GroundTheory.PAdicHodge.fg_ker_fontaineThetaInvertP hξ
  have hm : FB l k = Ideal.span {GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l ξ ^ k} := by
    rw [FB, ker_thB_eq, GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hξ,
      Ideal.span_singleton_pow]
  have h' : Ideal.span {GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l ξ ^ k} =
      (RingHom.ker (fontaineThetaInvertP _ l) ^ k).map
        (GroundTheory.PAdicHodge.toBDeRhamPlus _ l) := by
    rw [GroundTheory.PAdicHodge.ker_fontaineThetaInvertP hξ, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, map_pow]
    rfl
  obtain ⟨a0, ha0⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP _ l)) k b)
  have hz : b - GroundTheory.PAdicHodge.toBDeRhamPlus _ l a0 ∈ FB l k := by
    let I := RingHom.ker (fontaineThetaInvertP (↥(GroundTheory.PAdicHodge.normInteger ℂ_[l])) l)
    let b' : AdicCompletion I (Localization.Away (l : Wl l)) := b
    let c' : AdicCompletion I (Localization.Away (l : Wl l)) := algebraMap _ _ a0
    have e : (AdicCompletion.evalₐ I k) c' = Ideal.Quotient.mk _ a0 := by
      simp only [c']
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        AdicCompletion.evalₐ_of]
    have h1 : b' - c' ∈ RingHom.ker (AdicCompletion.evalₐ I k).toRingHom := by
      rw [RingHom.mem_ker]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]
      rw [e, ha0, sub_self]
    rw [GroundTheory.PAdicHodge.ker_adicCompletion_evalₐ hfg k] at h1
    rw [hm, h']
    exact h1
  obtain ⟨⟨w, ⟨_, c, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers ((l : Wl l))) a0
  refine ⟨c, w, ?_⟩
  have e : (l : Formalism.Per6.BdRp l) ^ c * GroundTheory.PAdicHodge.toBDeRhamPlus _ l
      (IsLocalization.mk' _ w (⟨(l : Wl l) ^ c, c, rfl⟩ : Submonoid.powers (l : Wl l))) = wB l w := by
    have h2 := IsLocalization.mk'_spec (Localization.Away (l : Wl l)) w
      (⟨(l : Wl l) ^ c, c, rfl⟩ : Submonoid.powers (l : Wl l))
    have h3 := congrArg (GroundTheory.PAdicHodge.toBDeRhamPlus _ l) h2
    rw [map_mul] at h3
    have h4 : GroundTheory.PAdicHodge.toBDeRhamPlus _ l (algebraMap (Wl l) (Localization.Away (l : Wl l)) ((l : Wl l) ^ c)) =
        (l : Formalism.Per6.BdRp l) ^ c := by
      simp only [map_pow, map_natCast]
    simp only [] at h3
    rw [h4] at h3
    rw [mul_comm]
    exact h3
  rw [← e, ← mul_sub]
  exact Ideal.mul_mem_left _ _ hz

theorem normL : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)),
    ∀ s ∈ latS K', ‖thB l s‖ ≤ 1 := by
  intro l _ K' s hs
  have hle : latS K' ≤ (GroundTheory.PAdicHodge.normInteger ℂ_[l]).comap (thB l) := by
    refine (Subring.closure_le).2 ?_
    rintro z (⟨a, rfl⟩ | ⟨x, ⟨hx, hi⟩, rfl⟩)
    · change thB l (wB l a) ∈ GroundTheory.PAdicHodge.normInteger ℂ_[l]
      have e : thB l (wB l a) = _ :=
        GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus (K := ℂ_[l]) l a
      rw [e]
      exact Subtype.property _
    · change thB l (rB l x) ∈ GroundTheory.PAdicHodge.normInteger ℂ_[l]
      have e : thB l (rB l x) = ((x : Om l) : ℂ_[l]) := GroundTheory.PAdicHodge.thetaAlgHom_algClToBdR l x
      rw [e, GroundTheory.PAdicHodge.mem_normInteger, PadicComplex.norm_extends,
        ← GlobalTheory.isIntegral_padicInt_iff_norm_le_one]
      exact hi
  exact GroundTheory.PAdicHodge.mem_normInteger.1 (hle hs)

theorem galL : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [Normal ℚ_[l] K']
    (g : GQ l), ∀ s ∈ latS K', actB g s ∈ latS K' := by
  intro l _ K' hn g s hs
  have hle : latS K' ≤ (latS K').comap (actB g) := by
    refine (Subring.closure_le).2 ?_
    rintro z (⟨a, rfl⟩ | ⟨x, ⟨hx, hi⟩, rfl⟩)
    · change actB g (wB l a) ∈ latS K'
      have e : actB g (wB l a) = wB l (Formalism.Per6.toBot g • a) :=
        GroundTheory.PAdicHodge.gal_smul_wittToBDeRhamPlus (Formalism.Per6.toBot g) a
      rw [e]
      exact wB_mem_latS K' _
    · change actB g (rB l x) ∈ latS K'
      have e : actB g (rB l x) = rB l (g x) :=
        GroundTheory.PAdicHodge.gal_smul_algClToBdR (Formalism.Per6.toBot g) x
      rw [e]
      refine rB_mem_latS K' ?_ (hi.map ((g : Om l →ₐ[ℚ_[l]] Om l).restrictScalars ℤ_[l]))
      exact (IntermediateField.normal_iff_forall_map_le.1 hn) (g : Om l →ₐ[ℚ_[l]] Om l) ⟨x, hx, rfl⟩
  exact hle hs

theorem xpowL : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) (x : Om l),
    x ∈ K' → ‖((x : Om l) : ℂ_[l])‖ < 1 →
    ∃ (N : ℕ) (y : Om l), 0 < N ∧ y ∈ K' ∧ IsIntegral ℤ_[l] y ∧ x ^ N = (l : Om l) * y := by
  intro l _ K' x hx h1
  rw [PadicComplex.norm_extends] at h1
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlp : 0 < ‖(l : Om l)‖ := norm_pos_iff.2 hl0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hlp h1
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · exfalso
      have hle : ‖(l : Om l)‖ ≤ 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
        exact Padic.norm_p_lt_one.le
      rw [pow_zero] at hN
      exact absurd hN (not_lt.2 hle)
    · exact h
  refine ⟨N, x ^ N / (l : Om l), hNpos, ?_, ?_, ?_⟩
  · refine div_mem (pow_mem hx N) ?_
    exact natCast_mem K' l
  · rw [GlobalTheory.isIntegral_padicInt_iff_norm_le_one, norm_div, norm_pow]
    exact (div_le_one hlp).2 hN.le
  · field_simp

end GlobalTheory.CompanionTheory.LTPer

namespace GlobalTheory.CompanionTheory.LTPer

theorem mem_FB_of_near {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (T : Finset (Formalism.Per6.BdRp l))
    (hS : ∀ s ∈ S, ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t)) (k : ℕ)
    (x : Formalism.Per6.BdRp l) (h : ∀ m : ℕ, ∃ s ∈ S, x - (l : Formalism.Per6.BdRp l) ^ m * s ∈ FB l k) :
    x ∈ FB l k := by
  choose cf af hcf using fun t : Formalism.Per6.BdRp l => keyL t k
  set c := T.sup cf with hc
  have hT : ∀ t ∈ T, (l : Formalism.Per6.BdRp l) ^ c * t -
      wB l ((l : Wl l) ^ (c - cf t) * af t) ∈ FB l k := by
    intro t ht
    have hle : cf t ≤ c := Finset.le_sup ht
    have e : (l : Formalism.Per6.BdRp l) ^ c * t - wB l ((l : Wl l) ^ (c - cf t) * af t) =
        (l : Formalism.Per6.BdRp l) ^ (c - cf t) * ((l : Formalism.Per6.BdRp l) ^ cf t * t - wB l (af t)) := by
      rw [map_mul, map_pow, map_natCast, mul_sub, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [e]
    exact Ideal.mul_mem_left _ _ (hcf t)
  have hSa : ∀ s ∈ S, ∃ a : Wl l, (l : Formalism.Per6.BdRp l) ^ c * s - wB l a ∈ FB l k := by
    intro s hs
    obtain ⟨a, rfl⟩ := hS s hs
    refine ⟨∑ t ∈ T, (l : Wl l) ^ (c - cf t) * af t * a t, ?_⟩
    rw [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun t ht => ?_
    have e : (l : Formalism.Per6.BdRp l) ^ c * (t * wB l (a t)) -
        wB l ((l : Wl l) ^ (c - cf t) * af t * a t) =
        ((l : Formalism.Per6.BdRp l) ^ c * t - wB l ((l : Wl l) ^ (c - cf t) * af t)) * wB l (a t) := by
      rw [map_mul (wB l) _ (a t)]; ring
    rw [e]
    exact Ideal.mul_mem_right _ _ (hT t ht)
  have hm : FB l k = IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) ^ k := by rw [FB, ker_thB_eq]
  rw [hm]
  refine GroundTheory.PAdicHodge.IsPerfectoidField.mem_maximalIdeal_pow_of_forall_sub_mem (K := ℂ_[l]) (p := l)
    fun M => ?_
  obtain ⟨s, hs, hx⟩ := h (M + c)
  obtain ⟨a, ha⟩ := hSa s hs
  refine ⟨a, ?_⟩
  rw [← hm]
  have e : x - (l : Formalism.Per6.BdRp l) ^ M * GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l a =
      (x - (l : Formalism.Per6.BdRp l) ^ (M + c) * s) +
        (l : Formalism.Per6.BdRp l) ^ M * ((l : Formalism.Per6.BdRp l) ^ c * s - wB l a) := by
    rw [pow_add, wB]; ring
  rw [e]
  exact add_mem hx (Ideal.mul_mem_left _ _ ha)

theorem FB_sep {l : ℕ} [Fact l.Prime] (x : Formalism.Per6.BdRp l) (h : ∀ k, x ∈ FB l k) : x = 0 := by
  refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l)) inferInstance x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← ker_thB_eq]
  exact h n

theorem FB_complete {l : ℕ} [Fact l.Prime] (x : ℕ → Formalism.Per6.BdRp l)
    (h : ∀ k, x (k + 1) - x k ∈ FB l k) : ∃ t, ∀ k, t - x k ∈ FB l k := by
  have hc : IsPrecomplete (IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l)) (Formalism.Per6.BdRp l) := inferInstance
  have hstep : ∀ m n, m ≤ n → x n - x m ∈ FB l m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : x (n + 1) - x n ∈ FB l m := Ideal.pow_le_pow_right hmn (h n)
      have := add_mem h1 ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨t, ht⟩ := hc.prec (f := x) (fun {m n} hmn => by
    rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← ker_thB_eq]
    exact hstep m n hmn)
  refine ⟨t, fun k => ?_⟩
  have := ht k
  rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← ker_thB_eq] at this
  exact this

theorem lattice_main : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] K'] [Normal ℚ_[l] K'],
    ∃ S : Subring (Formalism.Per6.BdRp l), (∀ a, wB l a ∈ S) ∧
      (∀ x ∈ K', IsIntegral ℤ_[l] x → rB l x ∈ S) ∧
      (∀ (g : GQ l), ∀ s ∈ S, actB g s ∈ S) ∧ (∀ s ∈ S, ‖thB l s‖ ≤ 1) ∧
      ∀ x ∈ K', IsIntegral ℤ_[l] x → x ≠ 0 → ‖((x : Om l) : ℂ_[l])‖ < 1 →
        PerEnv S (FB l) (rB l x) ∧ ∀ u : Tl l, u ≠ 0 → ∀ s ∈ S, tch l u ≠ rB l x * s := by
  intro l _ K' _ _
  refine ⟨latS K', wB_mem_latS K', fun x hx hi => rB_mem_latS K' hx hi, galL K', normL K', ?_⟩
  intro x hxK hxi hx0 hx1
  obtain ⟨T, hT, hS⟩ := latS_finite_span K'
  obtain ⟨N, y, hN, hyK, hyi, hxy⟩ := xpowL K' x hxK hx1
  have hϖ : rB l x ∈ latS K' := rB_mem_latS K' hxK hxi
  have hy : rB l y ∈ latS K' := rB_mem_latS K' hyK hyi
  have hϖy : rB l x ^ N = (l : Formalism.Per6.BdRp l) * rB l y := by
    rw [← map_pow, hxy, map_mul, map_natCast]
  have hnear : ∀ k x', (∀ m : ℕ, ∃ s ∈ latS K', x' - (l : Formalism.Per6.BdRp l) ^ m * s ∈ FB l k) → x' ∈ FB l k :=
    fun k x' h => mem_FB_of_near (latS K') T hS k x' h
  have hsep : ∀ x' : Formalism.Per6.BdRp l, (∀ m : ℕ, ∃ s ∈ latS K', x' = (l : Formalism.Per6.BdRp l) ^ m * s) → x' = 0 := by
    intro x' h
    refine FB_sep x' fun k => hnear k x' fun m => ?_
    obtain ⟨s, hs, e⟩ := h m
    exact ⟨s, hs, by rw [← e, sub_self]; exact zero_mem _⟩
  refine ⟨⟨by simp [FB], fun k => Ideal.pow_le_pow_right (Nat.le_succ k),
    fun a b => by rw [FB, FB, FB, pow_add], FB_sep, FB_complete,
    (IsUnit.map (rB l) (isUnit_iff_ne_zero.2 hx0)), hϖ, ?_, ?_⟩,
    tch_ne_mul_of_pow_eq (latS K') T (wB_mem_latS K') hT hS (rB l x) (rB l y) N hy hϖy⟩
  · exact PowerSeriesSum.sum_with_tails (wB l) l (latS K') T (wB_mem_latS K') hT hS hsep (rB l x) (rB l y) N hN hϖ hy hϖy
  · intro k x' _ h
    refine hnear k x' fun m => ?_
    obtain ⟨s, hs, e⟩ := h (N * m)
    refine ⟨rB l y ^ m * s, mul_mem (pow_mem hy m) hs, ?_⟩
    have e2 : rB l x ^ (N * m) * s = (l : Formalism.Per6.BdRp l) ^ m * (rB l y ^ m * s) := by
      rw [pow_mul, hϖy, mul_pow, mul_assoc]
    rwa [e2] at e

end GlobalTheory.CompanionTheory.LTPer

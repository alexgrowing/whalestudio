import Mathlib
import Formalism.SharpRestriction.Divisibility.ChainOperators.CutKapD
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.PropositionATypePrimesAdmissible
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.MainNotions

namespace Conj

open Formalism.BasicNotions.DV NumberField IsDedekindDomain

theorem valuation_conj (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    (D.plEq (D.what₂.places.conj w)).valuation D.what₂.LL x = (D.plEq w).valuation D.what₂.LL (star x) := by
  by_cases hx : x = 0
  · subst hx; rw [star_zero, map_zero, map_zero]
  have hs : star x ≠ 0 := by rwa [ne_eq, star_eq_zero]
  have h := D.conj_val w x
  rw [D.val_eq _ x hx, D.val_eq w (star x) hs] at h
  have h1 : vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by exact_mod_cast h
  unfold vAdd at h1
  have h2 := neg_inj.mp h1
  have n1 : (D.plEq (D.what₂.places.conj w)).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have n2 : (D.plEq w).valuation D.what₂.LL (star x) ≠ 0 := (Valuation.ne_zero_iff _).mpr hs
  rw [← WithZero.exp_log n1, h2, WithZero.exp_log n2]

theorem plEq_conj (D : D7) (w : D.what₂.places.Pl) :
    (D.plEq (D.what₂.places.conj w)).asIdeal = (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL) := by
  have hmem : ∀ x : 𝓞 D.what₂.LL, x ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL x ∈ (D.plEq w).asIdeal := by
    intro x
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL), valuation_conj]
    rfl
  apply le_antisymm
  · intro x hx
    have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.what₂.LL) ((hmem x).1 hx)
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO] at this
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, hmem, Formalism.DivisionValues.ValuationRepresentative.cO_cO]
    exact hy

theorem logWeight_conj (D : D7) (w : D.what₂.places.Pl) : SizeData₂.lwP (D.what₂.places.conj w) = SizeData₂.lwP w := by
  unfold SizeData₂.lwP lw
  rw [plEq_conj, Formalism.DivisionValues.ValuationRepresentative.absNorm_map_ringEquiv]

end Conj

section C2

open Formalism.BasicNotions.DV

variable {D : D7}

theorem Dpm_eq_fockDeg {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    LiftErrorLocal.Dpm D j = fockDeg D j := by
  unfold LiftErrorLocal.Dpm fockDeg
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e1 : ∀ a, |D.what₂.kaBig j τ a| = D.what₂.kaBig j τ a := fun a => by
    rw [← X.ka_big j h1 h2 τ a]; exact abs_of_nonneg (Int.natCast_nonneg _)
  have e2 : ∀ a, |D.what₂.kaSmall j τ a| = -D.what₂.kaSmall j τ a := fun a => by
    have h := X.ka_small j h1 h2 τ (Fin.rev a)
    rw [Fin.rev_rev] at h
    have h0 : D.what₂.kaSmall j τ a ≤ 0 := by
      have := Int.natCast_nonneg ((X.run j).ka.aM τ (Fin.rev a)); omega
    exact abs_of_nonpos h0
  simp only [e1, e2, Finset.sum_neg_distrib]
  ring

theorem normDecompositionCond_of_jetConsequence (L : SizeData₂ D) (EX : ErrX D) (C1 C2 C3 : ℝ) (h : LiftErrorLocal.JetConsequence D L EX C1 C2 C3)
    (hl : ∀ w : D.what₂.places.Pl, SizeData₂.lwP (D.what₂.places.conj w) = SizeData₂.lwP w) : WeightDegreeSizes.NormDecompositionCond D EX := by
  intro i u j hj S hS0
  have hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = D.host.g i := hS0
  have h2 := h.2.1 i
  set a : D.what₂.places.Pl → ℝ := fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) with ha
  have hac : ∀ w, a (D.what₂.places.conj w) = a w := fun w => by
    simp only [ha]; rw [hl w, PDVN.ramIdx_conj]
  have hmem : ∀ w, w ∈ S → D.what₂.places.conj w ∈ S := fun w hw => by
    rw [hS] at hw ⊢; rw [resChar_conj]; exact hw
  have hre : ∑ w ∈ S, a w * vNN EX i u j w = ∑ w ∈ S, a w * vNN EX i u j (D.what₂.places.conj w) := by
    refine Finset.sum_bij (fun w _ => D.what₂.places.conj w) (fun w hw => hmem w hw) ?_ ?_ ?_
    · intro w _ w' _ hww
      have := congrArg D.what₂.places.conj hww
      rwa [D.what₂.places.conj_conj, D.what₂.places.conj_conj] at this
    · intro w hw
      exact ⟨D.what₂.places.conj w, hmem w hw, D.what₂.places.conj_conj w⟩
    · intro w _
      rw [hac, D.what₂.places.conj_conj]
  have hsum : ∑ w ∈ S, SizeData₂.sz w (vNN EX i u j w) =
      ∑ w ∈ S, a w * (vNN EX i u j w + vNN EX i u j (D.what₂.places.conj w)) := by
    have e : ∀ w, SizeData₂.sz w (vNN EX i u j w) = a w * vNN EX i u j w + a w * vNN EX i u j w := fun w => by
      simp only [ha, SizeData₂.sz]; ring
    rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib]
    nth_rewrite 2 [hre]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have h3 : ∑ w ∈ S, a w * (vNN EX i u j w + vNN EX i u j (D.what₂.places.conj w)) =
      ∑ w ∈ S, a w * LiftErrorLocal.Dpi D u j :=
    Finset.sum_congr rfl fun w hw => by rw [h2 w ((hS w).1 hw) u j hj]
  have hm : ∑ w ∈ S, a w = Real.log (D.host.g i : ℝ) := factEtaMean D (D.host.g i) (D.host.g_prime i) S hS
  rw [hsum, h3, ← Finset.sum_mul, hm]
  unfold LiftErrorLocal.Dpi
  ring

end C2

section C2deg

open Formalism.BasicNotions.DV

variable {D : D7}

theorem deg_core {A B W f S0 S1 kN kT T b1 P Q : ℝ} (hA : |A| ≤ W + f * (P * S1) + T * (P * b1))
    (hB : |B| ≤ Q * f * (S0 + (kN + kT))) (hW : 0 ≤ W) (hf : 0 ≤ f) (hS0 : 0 ≤ S0) (hS : S0 ≤ S1) (hkN : 0 ≤ kN)
    (hkT : kT ≤ kN) (hT : 0 ≤ T) (hb : 0 ≤ b1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    |A - B| ≤ 2 * W + (P + 2 * Q) * (f * (S1 + kN) + T * b1) := by
  obtain ⟨a1, a2⟩ := abs_le.1 hA
  obtain ⟨c1, c2⟩ := abs_le.1 hB
  have h2 : Q * f * (S0 + (kN + kT)) ≤ Q * f * (S1 + 2 * kN) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hQ hf)
  have h5 : 0 ≤ Q * f * S1 := mul_nonneg (mul_nonneg hQ hf) (hS0.trans hS)
  have h3 : 0 ≤ P * (f * kN) := mul_nonneg hP (mul_nonneg hf hkN)
  have h4 : 0 ≤ Q * (T * b1) := mul_nonneg hQ (mul_nonneg hT hb)
  rw [abs_le]
  constructor <;> nlinarith

theorem degree_count_bound {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (L : SizeData₂ D) (EX : ErrX D) (C1 C2 C3 CD : ℝ)
    (hC : LiftErrorLocal.JetConsequence D L EX C1 C2 C3) (hD : LiftErrorLocal.ThetaAdjointPositiveScalar D L CD) (hk : KapDef D)
    (hw : ∀ j τ, 0 ≤ wj D j τ) (hSc : 0 ≤ L.Sc) (hη : 0 ≤ L.etaSz) (hb : 0 ≤ L.sc.b' / L.sc.x) :
    WeightDegreeSizes.DegreeCountBound D L (max C3 0 + 2 * max CD 0) := by
  classical
  intro u j hj
  have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
  obtain ⟨ha, hb', -⟩ := hC.2.2.2 u j hj
  have hd := hD hk j hj
  rw [← Dpm_eq_fockDeg X j hj'.1 hj'.2]
  have split : ∀ g : D.what₂.Tau → ℝ, ∑ τ, g τ =
      ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), g τ + ∑ t : D.host.TT, g (WeightDegreeSizes.tauOfTop D t) := by
    intro g
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => WeightDegreeSizes.NotTop D τ) g]
    congr 1
    convert WeightDegreeSizes.sum_top D g
  set S1 : ℝ := (D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz with hS1
  set b1 : ℝ := L.sc.b' / L.sc.x with hb1
  set P : ℝ := max C3 0 with hP
  have hP0 : 0 ≤ P := le_max_right _ _
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  have hmη : 0 ≤ (D.R.m : ℝ) * L.etaSz := mul_nonneg (Nat.cast_nonneg _) hη
  have hS0 : 0 ≤ (D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz := add_nonneg (mul_nonneg (Nat.cast_nonneg _) hSc) hmη
  have hS01 : (D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz ≤ S1 := by
    have : (D.R.m : ℝ) * L.etaSz ≤ (D.R.m : ℝ) * D.R.t * L.etaSz := by
      nlinarith [mul_nonneg (sub_nonneg.2 ht1) hmη]
    simp only [hS1]; linarith
  have hS1n : 0 ≤ S1 := le_trans hS0 hS01
  have hW : 0 ≤ ∑ τ, wj D j τ := Finset.sum_nonneg fun τ _ => hw j τ

  have hA : |(∑ τ, (nuAbs D u j τ - ((D.R.k : ℝ) - 1) * wj D j τ)) - WeightDegreeSizes.sumA L| ≤
      (∑ τ, wj D j τ) + (D.R.f : ℝ) * (P * S1) + (D.host.TT.card : ℝ) * (P * b1) := by
    have e : (∑ τ, (nuAbs D u j τ - ((D.R.k : ℝ) - 1) * wj D j τ)) - WeightDegreeSizes.sumA L =
        ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), ((nuAbs D u j τ - (D.R.k : ℝ) * wj D j τ) + wj D j τ) +
          ∑ t : D.host.TT, (nuAbs D u j (WeightDegreeSizes.tauOfTop D t) -
            ((L.aT t : ℝ) + ((D.R.k : ℝ) - 1) * wj D j (WeightDegreeSizes.tauOfTop D t))) := by
      rw [split, WeightDegreeSizes.sumA, add_sub_assoc, ← Finset.sum_sub_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun τ _ => by ring
      · exact Finset.sum_congr rfl fun t _ => by ring
    have b1' : |∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ),
        ((nuAbs D u j τ - (D.R.k : ℝ) * wj D j τ) + wj D j τ)| ≤
        ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), (P * S1 + wj D j τ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ hτ => ?_)
      have hn : WeightDegreeSizes.NotTop D τ := (Finset.mem_filter.1 hτ).2
      have h1 : |nuAbs D u j τ - (D.R.k : ℝ) * wj D j τ| ≤ C3 * S1 :=
        ha τ fun t ht => WeightDegreeSizes.not_notTop (D := D) (τ := τ) (t := t) ht hn
      have h2 : C3 * S1 ≤ P * S1 := mul_le_mul_of_nonneg_right (le_max_left _ _) hS1n
      obtain ⟨l1, l2⟩ := abs_le.1 h1
      have h0 := hw j τ
      rw [abs_le]
      constructor <;> linarith
    have b2' : |∑ t : D.host.TT, (nuAbs D u j (WeightDegreeSizes.tauOfTop D t) -
        ((L.aT t : ℝ) + ((D.R.k : ℝ) - 1) * wj D j (WeightDegreeSizes.tauOfTop D t)))| ≤
        ∑ _t : D.host.TT, (P * S1 + P * b1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
      have h1 : |nuAbs D u j (WeightDegreeSizes.tauOfTop D t) -
          ((L.aT t : ℝ) + ((D.R.k : ℝ) - 1) * wj D j (WeightDegreeSizes.tauOfTop D t))| ≤ C3 * (S1 + b1) :=
        hb' (WeightDegreeSizes.tauOfTop D t) t (WeightDegreeSizes.isTopAt_tauOfTop D t)
      have h2 : C3 * (S1 + b1) ≤ P * (S1 + b1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hS1n hb)
      linarith
    have c1 : ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), (P * S1 + wj D j τ) +
        ∑ _t : D.host.TT, (P * S1 + P * b1) ≤
        (∑ τ, wj D j τ) + (D.R.f : ℝ) * (P * S1) + (D.host.TT.card : ℝ) * (P * b1) := by
      have s1 : ∑ _τ : D.what₂.Tau, P * S1 = ∑ _τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), P * S1 +
          ∑ _t : D.host.TT, P * S1 := split fun _ => P * S1
      rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at s1
      have s2 : ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), wj D j τ ≤ ∑ τ, wj D j τ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun τ _ _ => hw j τ
      have s3 : ∑ _t : D.host.TT, P * b1 = (D.host.TT.card : ℝ) * (P * b1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, s3]
      linarith
    rw [e]
    obtain ⟨l1, l2⟩ := abs_le.1 b1'
    obtain ⟨l3, l4⟩ := abs_le.1 b2'
    rw [abs_le]
    constructor <;> linarith
  have hkN : 0 ≤ (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D := mul_nonneg (Nat.cast_nonneg _) (by unfold Formalism.MainNotions.G.Nm; exact Nat.cast_nonneg _)
  have hkt : 0 ≤ (D.R.k : ℝ) * D.R.t := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htN : (D.R.k : ℝ) * D.R.t ≤ (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D := by
    have h0 : D.R.t ≤ D.R.N D.R.m := by
      have := D.R.two_le_m
      unfold Formalism.BasicNotions.Ranks.N
      nlinarith
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    unfold Formalism.MainNotions.G.Nm
    exact_mod_cast h0
  have hB : |(LiftErrorLocal.Dpm D j : ℝ) - ∑ τ, ((D.R.k : ℝ) - 1) * wj D j τ| ≤
      max CD 0 * D.R.f * (((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz) +
        ((D.R.k : ℝ) * Formalism.MainNotions.G.Nm D + (D.R.k : ℝ) * D.R.t)) := by
    refine hd.trans ?_
    have : CD * (D.R.f : ℝ) ≤ max CD 0 * D.R.f := mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    have e : (D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz + (D.R.k : ℝ) * ((D.R.N D.R.m : ℝ) + D.R.t) =
        ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz) + ((D.R.k : ℝ) * Formalism.MainNotions.G.Nm D + (D.R.k : ℝ) * D.R.t) := by
      unfold Formalism.MainNotions.G.Nm; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right this (add_nonneg hS0 (add_nonneg hkN hkt))
  have key := deg_core hA hB hW (Nat.cast_nonneg _) hS0 hS01 hkN htN (Nat.cast_nonneg _) hb hP0 (le_max_right CD 0)
  have e1 : (∑ τ, nuAbs D u j τ) - (LiftErrorLocal.Dpm D j : ℝ) - WeightDegreeSizes.sumA L =
      ((∑ τ, (nuAbs D u j τ - ((D.R.k : ℝ) - 1) * wj D j τ)) - WeightDegreeSizes.sumA L) -
        ((LiftErrorLocal.Dpm D j : ℝ) - ∑ τ, ((D.R.k : ℝ) - 1) * wj D j τ) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e1]
  refine key.trans (le_of_eq ?_)
  unfold WeightDegreeSizes.errG
  simp only [hS1, hb1]
  ring

end C2deg

section secondOrderBound

variable {eps : ℝ} (Fm : FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)

include XF in

theorem degree_weight_family_of_constant_D (C1 C2 C3 CD : ℝ)
    (h : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.JetConsequence (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 C3 ∧ LiftErrorLocal.ThetaAdjointPositiveScalar (Fm.D x i) (Fm.L x i) CD)
    (hs : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, ∀ j τ, 0 ≤ wj (Fm.D x i) j τ)
    (rest : ∃ Cg CT CG Cd CI x0 : ℝ, 0 ≤ Cg ∧ ∀ x, x0 ≤ x → ∀ i : Fm.Ix x,
      WeightDegreeSizes.TypePrimeSizeBound (Fm.D x i) (Fm.L x i) Fm.cX.err (max C3 0 + 2 * max CD 0) Cg ∧
      WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) CT ∧ WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) CG ∧
      WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) Cd ∧ WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err CI) :
    ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LocalQuadraticParts.adm11 (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨xa, h⟩ := h
  obtain ⟨xb, hs⟩ := hs
  obtain ⟨Cg, CT, CG, Cd, CI, xc, hCg, rest⟩ := rest
  refine WeightDegreeSizes.secondComplement_family_of_inputs Fm ⟨max C3 0 + 2 * max CD 0, Cg, CT, CG, Cd, CI, max xa (max xb xc), hCg, fun x hx hx1 i => ?_⟩
  have ha : xa ≤ x := le_trans (le_max_left _ _) hx
  have hb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hc' : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨pC, pD⟩ := h x hx1 ha i
  obtain ⟨r2, r3, r4, r5, r6⟩ := rest x hc' i
  exact ⟨fun u i' h => (Fm.D x i).T_ne_g u i' h.symm, normDecompositionCond_of_jetConsequence _ _ C1 C2 C3 pC (Conj.logWeight_conj _),
    degree_count_bound (XF x hx1 i) _ _ C1 C2 C3 CD pC pD (Fm.ex x hx1 i).kap_def (hs x hb i) (Fm.L x i).Sc_pos.le
      (Fm.L x i).etaSz_pos.le (div_nonneg (Fm.L x i).sc.b'_pos.le (Fm.L x i).sc.x_pos.le), r2, r3, r4, r5, r6⟩

noncomputable abbrev weightDegreeConstant : ℝ := CutKapD.kappa_degree_bound_holds.choose

include XF in

theorem degree_weight_family_of_constant (C1 C2 C3 : ℝ)
    (h : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, LiftErrorLocal.JetConsequence (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 C3)
    (hs : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, ∀ j τ, 0 ≤ wj (Fm.D x i) j τ)
    (rest : ∃ Cg CT CG Cd CI x0 : ℝ, 0 ≤ Cg ∧ ∀ x, x0 ≤ x → ∀ i : Fm.Ix x,
      WeightDegreeSizes.TypePrimeSizeBound (Fm.D x i) (Fm.L x i) Fm.cX.err (max C3 0 + 2 * max weightDegreeConstant 0) Cg ∧
      WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) CT ∧ WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) CG ∧
      WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) Cd ∧ WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err CI) :
    ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LocalQuadraticParts.adm11 (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨x0, h⟩ := h
  exact degree_weight_family_of_constant_D Fm XF C1 C2 C3 weightDegreeConstant
    ⟨x0, fun x hx h0 i => ⟨h x hx h0 i, CutKapD.kappa_degree_bound_holds.choose_spec (Fm.D x i) (Fm.L x i)⟩⟩ hs rest

end secondOrderBound

end Formalism.MainNotions.DIV

end

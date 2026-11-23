import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)

namespace StarEntryOperators

theorem lowOp_int {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 C : ℕ} (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (hT : ∀ c i a, ‖T c i a‖ ≤ 1) : ∀ n, ‖MvPolynomial.coeff n (lowOp l sf T I)‖ ≤ 1 := by
  have h : lowOp l sf T I ∈ opInt K (ZV ν r0 r1) := by
    unfold lowOp minorAt
    refine Subring.prod_mem _ fun c _ => ?_
    rw [Matrix.det_apply]
    refine Subring.sum_mem _ fun π _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem ?_ _
    refine Subring.prod_mem _ fun r _ => ?_
    rw [Matrix.of_apply]
    refine Subring.sum_mem _ fun a _ => ?_
    intro κ
    classical
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, norm_mul]
    refine mul_le_one₀ (hT _ _ _) (norm_nonneg _) ?_
    split_ifs <;> simp
  exact h

theorem deg_ZV {ν r0 r1 : ℕ} [NeZero ν] (n : ZV ν r0 r1 →₀ ℕ) :
    n.degree = ∑ s, ∑ x : Fin r0 × Fin r1, n (s, x) := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]

theorem lowOp_deg {K : Type} [Field K] (hM : MinorProdDegree) {ν r0 r1 C : ℕ} [NeZero ν]
    (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
    (I : ∀ c, Fin (l c) → Fin r1) (n : ZV ν r0 r1 →₀ ℕ) (hn : n ∈ (lowOp l sf T I).support) :
    (∀ s, ∑ x : Fin r0 × Fin r1, n (s, x) = lsN l sf s) ∧ n.degree = ∑ s, lsN l sf s := by
  have hs := hM K (ZMod (2 * ν)) r0 r1 C l sf T I n hn
  refine ⟨hs, ?_⟩
  rw [deg_ZV]
  exact Finset.sum_congr rfl fun s _ => hs s

theorem lowOp_hom {K : Type} [Field K] (hM : MinorProdDegree) {ν r0 r1 C : ℕ} [NeZero ν]
    (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
    (I : ∀ c, Fin (l c) → Fin r1) : (lowOp l sf T I).IsHomogeneous (∑ s, lsN l sf s) := by
  intro n hn
  have h := (lowOp_deg hM l sf T I n (MvPolynomial.mem_support_iff.mpr hn)).2
  rw [← h, Finsupp.degree_eq_weight_one]
  rfl

section Lin

variable {K : Type} [Field K] {ν r0 r1 : ℕ}

def Amat (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) :
    TpV ν r1 ⊕ ZV ν r0 r1 → ZV ν r0 r1 → K
  | Sum.inl t, x => if t = (x.1, x.2.2) then (if x.1 ∈ TT then ξ x.1 x.2.1 else 0) else 0
  | Sum.inr y, x => if y = x then 1 else 0

theorem zSub_eq [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (x : ZV ν r0 r1) :
    zSub TT ξ x = ∑ i, MvPowerSeries.C (Amat TT ξ i x) * MvPowerSeries.X i := by
  rw [Fintype.sum_sum_type, Finset.sum_eq_single (x.1, x.2.2), Finset.sum_eq_single x]
  · simp only [Amat, if_true, map_one, one_mul, zSub]
    rw [add_comm]
    split_ifs <;> simp
  · intro y _ hy
    simp [Amat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro y _ hy
    simp [Amat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem img_inr [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (y : ZV ν r0 r1) :
    (∑ x, MvPolynomial.C (Amat TT ξ (Sum.inr y) x) * MvPolynomial.X x :
      MvPolynomial (ZV ν r0 r1) K) = MvPolynomial.X y := by
  rw [Finset.sum_eq_single y]
  · simp [Amat]
  · intro x _ hx
    simp [Amat, Ne.symm hx]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem img_inl [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (t : TpV ν r1) :
    (∑ x, MvPolynomial.C (Amat TT ξ (Sum.inl t) x) * MvPolynomial.X x :
      MvPolynomial (ZV ν r0 r1) K) = if t.1 ∈ TT then topForm ξ t else 0 := by
  obtain ⟨s, b⟩ := t
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
  · rw [Fintype.sum_prod_type]
    have : ∀ a : Fin r0, (∑ b' : Fin r1, MvPolynomial.C (Amat TT ξ (Sum.inl (s, b)) (s, a, b')) *
        MvPolynomial.X (s, a, b') : MvPolynomial (ZV ν r0 r1) K) =
        if s ∈ TT then MvPolynomial.C (ξ s a) * MvPolynomial.X (s, a, b) else 0 := by
      intro a
      rw [Finset.sum_eq_single b]
      · simp only [Amat, if_true]
        split_ifs <;> simp
      · intro b' _ hb'
        simp [Amat, Ne.symm hb']
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [this, topForm]
    split_ifs <;> simp
  · intro s' _ hs'
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [Amat, Ne.symm hs']
  · intro h; exact absurd (Finset.mem_univ _) h

theorem aeval_entry [NeZero ν] {C : ℕ} (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (he : ∀ x : TpV ν r1, x.1 ∉ TT → e x = 0)
    (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
    (I : ∀ c, Fin (l c) → Fin r1) :
    MvPolynomial.aeval (fun i : TpV ν r1 ⊕ ZV ν r0 r1 =>
        (∑ x, MvPolynomial.C (Amat TT ξ i x) * MvPolynomial.X x : MvPolynomial (ZV ν r0 r1) K))
      (topMonoP (Finsupp.equivFunOnFinite.symm e) * lowPoly (lowOp l sf T I)) =
      entryOp ξ e l sf T I := by
  rw [map_mul, entryOp]
  congr 1
  · rw [topMonoP, MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [img_inl, Finsupp.equivFunOnFinite_symm_apply_apply]
    split_ifs with h
    · rfl
    · rw [he x h, pow_zero, pow_zero]
  · rw [lowPoly, MvPolynomial.aeval_rename]
    have : ((fun i : TpV ν r1 ⊕ ZV ν r0 r1 =>
        (∑ x, MvPolynomial.C (Amat TT ξ i x) * MvPolynomial.X x : MvPolynomial (ZV ν r0 r1) K)) ∘
        Sum.inr) = MvPolynomial.X := by
      funext y
      exact img_inr TT ξ y
    rw [this, MvPolynomial.aeval_X_left_apply]

theorem cc_zSub (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (x : ZV ν r0 r1) :
    MvPowerSeries.constantCoeff (zSub (r1 := r1) TT ξ x) = 0 := by
  unfold zSub
  split_ifs <;> simp

theorem cc_hhS [NeZero ν] {p : ℕ} (hp : p ≠ 0) (u : ZMod (2 * ν) → K) :
    MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p u) = 0 := by
  have h : ∀ (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1),
      MvPowerSeries.constantCoeff (sPos (K := K) p s ab) = 0 := by
    intro s ab
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change (∑ l ∈ range ((0 : ZV ν r0 r1 →₀ ℕ).degree + 1),
      if (0 : ZV ν r0 r1 →₀ ℕ) = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l)
        then (-1 : K) ^ l else 0) = 0
    refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
    have := Finsupp.single_eq_zero.1 h.symm
    exact (pow_ne_zero l (pow_ne_zero 2 hp)) this
  simp [hhS, map_sum, h]

end Lin

theorem int_zSub {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}
    (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (hξ : ∀ s a, ‖ξ s a‖ ≤ 1)
    (x : ZV ν r0 r1) : Integral (zSub (r1 := r1) TT ξ x) := by
  intro n
  classical
  unfold zSub
  rw [map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  · split_ifs
    · rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, norm_mul]
      refine mul_le_one₀ (hξ _ _) (norm_nonneg _) ?_
      split_ifs <;> simp
    · simp

theorem norm_nat {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {m : ℕ} (hm : m ≠ 0) :
    ‖(m : K)‖ = (p : ℝ) ^ (-(padicValNat p m : ℝ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : ‖(p : K)‖ < 1 := by
    rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1
  rw [Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp hlt hm, hnp,
    Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]

theorem norm_prod_fact {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {α : Type} (s : Finset α) (f : α → ℕ) :
    ‖((∏ x ∈ s, (f x).factorial : ℕ) : K)‖ =
      (p : ℝ) ^ (-(∑ x ∈ s, (padicValNat p (f x).factorial : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Nat.cast_prod, norm_prod, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hp0]
  exact Finset.prod_congr rfl fun x _ => norm_nat hp hnp (Nat.factorial_ne_zero _)

theorem norm_le_of_dvd {K : Type} [NormedField K] [IsUltrametricDist K] {a b : ℕ} (h : a ∣ b) :
    ‖(b : K)‖ ≤ ‖(a : K)‖ := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K c)

theorem star_norm {K : Type} [NormedField K] [IsUltrametricDist K] (hS : StarArith)
    {p ν r0 r1 E : ℕ} [NeZero ν] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (TT : Finset (ZMod (2 * ν))) (e : TpV ν r1 → ℕ) (ls : ZMod (2 * ν) → ℕ)
    (he : ∀ x : TpV ν r1, x.1 ∉ TT → e x = 0) (β : KapI ν r1 E →₀ ℕ)
    (hβ : ∀ k, β k ≠ 0 → k.1 ∈ TT) (n : ZV ν r0 r1 →₀ ℕ) (i0 i2 : ℕ)
    (h1 : ∀ s, ∑ x : Fin r0 × Fin r1, n (s, x) ≤ ls s) (h2 : n.degree + ∑ k, β k = ∑ s, ls s)
    (h3 : ∀ k : KapI ν r1 E, p ^ (2 * k.2.1.val + 1) * β k ≤ e (k.1, k.2.2))
    (h4 : p * i2 ≤ n.degree) :
    (p : ℝ) ^ (i0 + ∑ k, β k + i2) * ‖((mfact (Finsupp.equivFunOnFinite.symm e) : ℕ) : K)‖ *
        ‖(((∑ k, β k).factorial : ℕ) : K)‖ * ‖((mfact n : ℕ) : K)‖ ≤
      (p : ℝ) ^ (-(gamP p * ∑ s ∈ TT, (alN e s : ℝ) - (i0 : ℝ) - (∑ k, (β k : ℝ)) -
        deLoss p r0 r1 TT (alN e) ls + rhoP p * ∑ s, ((alN e s : ℝ) + ls s))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le

  set i : ZMod (2 * ν) → ℕ → ℕ := fun s e' =>
    if h : e' < E then ∑ b, β (s, ⟨e', h⟩, b) else 0 with hi
  have hirange : ∀ s, ∑ e' ∈ range E, i s e' = ∑ ε : Fin E, ∑ b, β (s, ε, b) := by
    intro s
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun ε _ => ?_
    simp only [hi, ε.2, dif_pos]
  have hβsum : ∑ k, β k = ∑ s, ∑ e' ∈ range E, i s e' := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hirange, Fintype.sum_prod_type]
  have hioff : ∀ s, s ∉ TT → ∀ e', i s e' = 0 := by
    intro s hs e'
    simp only [hi]
    split_ifs with h
    · refine Finset.sum_eq_zero fun b _ => ?_
      by_contra hne
      exact hs (hβ _ hne)
    · rfl
  have key := hS (ZMod (2 * ν)) p r0 r1 TT (alN e) ls (fun s b => e (s, b)) (fun s x => n (s, x)) i
    (range E) i0 i2 hp
    (by
      intro s hs
      exact Finset.sum_eq_zero fun b _ => he (s, b) hs)
    (fun s => rfl) h1
    (by
      intro s e' he'
      simp only [hi]
      rw [dif_neg (by simpa using he')])
    hioff
    (by
      intro s e'
      simp only [hi]
      split_ifs with h
      · rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun b _ => h3 (s, ⟨e', h⟩, b)
      · simp)
    (by rw [← hβsum, ← deg_ZV, h2])
    (by rw [← h2]; exact h4.trans (Nat.le_add_right _ _))

  have N1 : ‖((mfact (Finsupp.equivFunOnFinite.symm e) : ℕ) : K)‖ =
      (p : ℝ) ^ (-(∑ s, ∑ b, (padicValNat p (e (s, b)).factorial : ℝ))) := by
    have : mfact (Finsupp.equivFunOnFinite.symm e) = ∏ x ∈ univ, (e x).factorial := by
      unfold mfact
      rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
      rfl
    rw [this, norm_prod_fact hp hnp, Fintype.sum_prod_type]
  have N3 : ‖((mfact n : ℕ) : K)‖ =
      (p : ℝ) ^ (-(∑ s, ∑ x, (padicValNat p (n (s, x)).factorial : ℝ))) := by
    have : mfact n = ∏ x ∈ univ, (n x).factorial := by
      unfold mfact
      rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
    rw [this, norm_prod_fact hp hnp, Fintype.sum_prod_type]
  have N2 : ‖(((∑ k, β k).factorial : ℕ) : K)‖ ≤
      (p : ℝ) ^ (-(∑ s, ∑ e' ∈ range E, (padicValNat p (i s e').factorial : ℝ))) := by
    have hdvd : (∏ x ∈ (univ : Finset (ZMod (2 * ν))) ×ˢ range E, (i x.1 x.2).factorial) ∣
        (∑ k, β k).factorial := by
      rw [hβsum, ← Finset.sum_product']
      exact Nat.prod_factorial_dvd_factorial_sum _ _
    refine (norm_le_of_dvd hdvd).trans (le_of_eq ?_)
    rw [norm_prod_fact hp hnp, Finset.sum_product]
  have hTTsum : ∑ s ∈ TT, ∑ e' ∈ range E, (i s e' : ℝ) = ∑ s, ∑ e' ∈ range E, (i s e' : ℝ) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => ?_
    exact Finset.sum_eq_zero fun e' _ => by rw [hioff s hs e', Nat.cast_zero]
  have hβR : (∑ k, (β k : ℝ)) = ∑ s, ∑ e' ∈ range E, (i s e' : ℝ) := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hβsum
    simpa [Nat.cast_sum] using this
  rw [N1, N3]
  calc (p : ℝ) ^ (i0 + ∑ k, β k + i2) *
          (p : ℝ) ^ (-(∑ s, ∑ b, (padicValNat p (e (s, b)).factorial : ℝ))) *
          ‖(((∑ k, β k).factorial : ℕ) : K)‖ *
          (p : ℝ) ^ (-(∑ s, ∑ x, (padicValNat p (n (s, x)).factorial : ℝ)))
      ≤ (p : ℝ) ^ (((i0 + ∑ k, β k + i2 : ℕ) : ℝ)) *
          (p : ℝ) ^ (-(∑ s, ∑ b, (padicValNat p (e (s, b)).factorial : ℝ))) *
          (p : ℝ) ^ (-(∑ s, ∑ e' ∈ range E, (padicValNat p (i s e').factorial : ℝ))) *
          (p : ℝ) ^ (-(∑ s, ∑ x, (padicValNat p (n (s, x)).factorial : ℝ))) := by
        rw [Real.rpow_natCast]
        gcongr
    _ = (p : ℝ) ^ (((i0 + ∑ k, β k + i2 : ℕ) : ℝ) +
          -(∑ s, ∑ b, (padicValNat p (e (s, b)).factorial : ℝ)) +
          -(∑ s, ∑ e' ∈ range E, (padicValNat p (i s e').factorial : ℝ)) +
          -(∑ s, ∑ x, (padicValNat p (n (s, x)).factorial : ℝ))) := by
        rw [Real.rpow_add hp0, Real.rpow_add hp0, Real.rpow_add hp0]
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
        rw [hTTsum] at key
        push_cast
        rw [hβR]
        linarith

end StarEntryOperators

theorem EntryStar_of (hT : TermBound) (hH : HhDecomp) (hC : ClassSubst)
    (hJ : Formalism.DworkPowerSeriesWeights.JetPairLin.{0}) (hS : StarArith) (hD : HasseDegree) (hM : MinorProdDegree) :
    EntryStar := by
  intro K _ _ p ν r0 r1 C _ u F TT ξ e l sf T I hyp
  obtain ⟨hp, hp2, hnp, hu, hF, hξ, hTn, he⟩ := hyp
  have hD0 : ∀ D : ℕ, D < p ^ (2 * (D + 1)) := fun D =>
    (Nat.lt_pow_self hp.one_lt).trans_le (Nat.pow_le_pow_right hp.pos (by omega))
  obtain ⟨Z, Y, hZ, hY, hZlow, hdec⟩ := hH K p ν r0 r1
    ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s + 1)
    ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s) u TT ξ hp hp2 hnp hu hξ (hD0 _)
  have hcc : MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p u) = 0 :=
    StarEntryOperators.cc_hhS hp.ne_zero u
  have hcls := hC K (ZV ν r0 r1) (TpV ν r1 ⊕ ZV ν r0 r1) (p : K) (hhS p u) F (zSub TT ξ) hcc
    (StarEntryOperators.cc_zSub TT ξ) (StarEntryOperators.int_zSub TT ξ hξ) hF
  have hcc' : MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (zSub TT ξ) (hhS (r0 := r0) (r1 := r1) p u)) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (StarEntryOperators.cc_zSub TT ξ))
      (StarEntryOperators.cc_zSub TT ξ) hcc
  have hjet : jetPair (topMonoP (Finsupp.equivFunOnFinite.symm e) * lowPoly (lowOp l sf T I))
      (MvPowerSeries.subst (zSub TT ξ) F) = jetPair (entryOp ξ e l sf T I) F := by
    have hz : (zSub TT ξ : ZV ν r0 r1 → _) = fun x =>
        ∑ i, MvPowerSeries.C (StarEntryOperators.Amat TT ξ i x) * MvPowerSeries.X i :=
      funext fun x => StarEntryOperators.zSub_eq TT ξ x
    rw [hz, hJ K (TpV ν r1 ⊕ ZV ν r0 r1) (ZV ν r0 r1) (StarEntryOperators.Amat TT ξ),
      StarEntryOperators.aeval_entry TT ξ e he]
  have one_pow_le : ∀ (a : K) (m : ℕ), ‖a‖ ≤ 1 → ‖a ^ m‖ ≤ 1 := fun a m ha => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have hsgn : ∀ m : ℕ, ‖(-1 : K) ^ m‖ ≤ 1 := fun m => one_pow_le _ _ (by simp)
  have hTB := hT K (TpV ν r1) (ZV ν r0 r1)
    (PhiI ν r0 r1 ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s + 1))
    (KapI ν r1 ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s + 1)) p
    ((Finsupp.equivFunOnFinite.symm e).degree + ∑ s, lsN l sf s) (∑ s, lsN l sf s)
    (MvPowerSeries.subst (zSub TT ξ) (hhS p u)) (MvPowerSeries.subst (zSub TT ξ) F) Z Y
    (aAof p u TT ξ) (dAof p) (aBof u TT) (dBof p) (bBof p ξ) (Finsupp.equivFunOnFinite.symm e)
    (lowOp l sf T I) hp hnp hcc' hcls
    (by
      intro φ
      unfold aAof
      split_ifs
      · rw [norm_mul, norm_mul, norm_mul]
        exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (hu _) (norm_nonneg _) (hsgn _))
          (norm_nonneg _) (one_pow_le _ _ (hξ _ _))) (norm_nonneg _) (one_pow_le _ _ (hξ _ _))
      · simp)
    (by
      intro k
      unfold aBof
      split_ifs
      · rw [norm_mul]
        exact mul_le_one₀ (hu _) (norm_nonneg _) (hsgn _)
      · simp)
    (by
      intro k x
      unfold bBof colDir
      split_ifs
      · exact one_pow_le _ _ (hξ _ _)
      · simp)
    hZ hY hZlow hdec (StarEntryOperators.lowOp_int l sf T I hTn) (StarEntryOperators.lowOp_hom hM l sf T I) rfl
  rw [hjet] at hTB
  rcases hTB with h0 | ⟨α, β, i2, n, hn, hα, hβ, htop, hi2, hbound⟩
  · exact Or.inl h0
  right
  have hβT : ∀ k, β k ≠ 0 → k.1 ∈ TT := by
    intro k hk
    by_contra hkT
    exact hβ k hk (by unfold aBof; rw [if_neg hkT])
  obtain ⟨n0, hn0, hle, hdeg⟩ := hD K (ZV ν r0 r1) _ (bBof p ξ) β (lowOp l sf T I) n hn
  obtain ⟨hn0s, hn0d⟩ := StarEntryOperators.lowOp_deg hM l sf T I n0 hn0
  refine ⟨_, α, β, ?_, hβT, ?_, ?_, ?_⟩
  · intro φ hφ
    by_contra hφT
    exact hα φ hφ (by unfold aAof; rw [if_neg hφT])
  · intro τ
    have := htop τ
    rwa [Finsupp.equivFunOnFinite_symm_apply_apply] at this
  · intro h0
    rw [h0] at hn
    simp at hn
  · refine hbound.trans ?_
    have := StarEntryOperators.star_norm (K := K) hS hp hnp TT e (lsN l sf) he β hβT n (∑ φ, α φ) i2
      (fun s => (Finset.sum_le_sum fun x _ => hle (s, x)).trans (hn0s s).le)
      (by rw [hdeg, hn0d])
      (by
        intro k
        have h := htop (k.1, k.2.2)
        rw [Finsupp.equivFunOnFinite_symm_apply_apply] at h
        refine le_trans ?_ ((Nat.le_add_left _ _).trans h)
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum
          (f := fun k' => β k' * dBof p k' (k.1, k.2.2)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ k))
        simp only [dBof, Finsupp.single_eq_same]
        rw [mul_comm])
      hi2
    rw [Nat.cast_sum] at this
    exact this

end Formalism.InvariantFactorPaths.G7

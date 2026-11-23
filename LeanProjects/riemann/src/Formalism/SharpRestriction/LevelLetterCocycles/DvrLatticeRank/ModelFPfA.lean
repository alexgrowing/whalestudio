import Formalism.SharpRestriction.LevelLetterCocycles.ExpansionFormAll

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34

section Ser

variable {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem finsum_mem_sub {ι : Type} (S : Submodule LL V) (t : ι → V) (ht : ∀ j, t j ∈ S) :
    ∑ᶠ j, t j ∈ S := by
  classical
  by_cases h : (Function.support t).Finite
  · rw [finsum_eq_sum _ h]
    exact Submodule.sum_mem _ fun j _ => ht j
  · rw [finsum_of_infinite_support h]
    exact Submodule.zero_mem _

theorem serMul_eq_sum (g : PowerSeries LL) (f : ℤ → V) (m : ℤ) (hf : ∀ k < m, f k = 0)
    (i : ℤ) (N : ℕ) (hN : i - m < N) :
    serMul g f i = ∑ j ∈ Finset.range N, PowerSeries.coeff j g • f (i - j) := by
  unfold serMul
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hj ⊢
  by_contra hjN
  push_neg at hjN
  apply hj
  rw [hf (i - j) (by omega), smul_zero]

theorem serMul_one (f : ℤ → V) (i : ℤ) : serMul (1 : PowerSeries LL) f i = f i := by
  unfold serMul
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem serMul_mem (S : ℤ → Submodule LL V) (hS : Monotone S) (g : PowerSeries LL) (m : ℕ)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) (f : ℤ → V) (hf : ∀ i, f i ∈ S i) (i : ℤ) :
    serMul g f i ∈ S (i - m) := by
  unfold serMul
  apply finsum_mem_sub
  intro j
  by_cases hj : j < m
  · rw [hg j hj, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (hS (by omega) (hf (i - j)))

theorem serMul_inv (S : ℤ → Submodule LL V) (hS : Monotone S) (g : PowerSeries LL) (m : ℕ)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) (hgm : PowerSeries.coeff m g ≠ 0) (f : ℤ → V)
    (m₀ : ℤ) (hf0 : ∀ k < m₀, f k = 0) (hF : ∀ i, serMul g f (i + m) ∈ S i) (i : ℤ) :
    f i ∈ S i := by
  have key : ∀ i, (∀ i' < i, f i' ∈ S i') → f i ∈ S i := by
    intro i ih
    by_cases hi : i < m₀
    · rw [hf0 i hi]; exact Submodule.zero_mem _
    push_neg at hi
    have hN : i + m - m₀ < (((i + m - m₀).toNat + m + 1 : ℕ) : ℤ) := by omega
    have hsum := serMul_eq_sum g f m₀ hf0 (i + m) ((i + m - m₀).toNat + m + 1) hN
    have hmN : m ∈ Finset.range ((i + m - m₀).toNat + m + 1) := Finset.mem_range.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ hmN] at hsum
    have hrest : ∑ j ∈ (Finset.range ((i + m - m₀).toNat + m + 1)).erase m,
        PowerSeries.coeff j g • f (i + m - j) ∈ S i := by
      refine Submodule.sum_mem _ fun j hj => ?_
      have hjm : j ≠ m := Finset.ne_of_mem_erase hj
      rcases Nat.lt_or_gt_of_ne hjm with hlt | hgt
      · rw [hg j hlt, zero_smul]; exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (hS (by omega) (ih _ (by omega)))
    have hmain : PowerSeries.coeff m g • f i ∈ S i := by
      have h1 := hF i
      rw [hsum] at h1
      have h2 := Submodule.sub_mem _ h1 hrest
      simp only [add_sub_cancel_right] at h2
      simpa using h2
    exact (Submodule.smul_mem_iff _ hgm).mp hmain
  have hall : ∀ n : ℕ, ∀ i, i < m₀ + n → f i ∈ S i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [hf0 i (by simpa using hi)]
      exact Submodule.zero_mem _
    | succ n ihn =>
      intro i hi
      apply key
      intro i' hi'
      exact ihn i' (by push_cast at hi; omega)
  exact hall ((i - m₀).toNat + 1) i (by omega)

end Ser

section Lev

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem lev_letE (c : ZMod n) (ζ : LL) : W.lev c ζ (letE c : LetA O n) = 1 := by
  have h1 : W.lev c ζ (1 - letE c : LetA O n) = 0 :=
    W.lev_letter c ζ _ (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h1
  exact h1.symm

theorem levN_eq_serMul (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T))
    (k : ℤ) : W.levN T c ζ (a • x) k = serMul (W.lev c ζ a) (W.levN T c ζ x) k :=
  W.levN_smul T c ζ a x k

theorem levN_letE (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ) :
    W.levN T c ζ ((letE c : LetA O n) • x) k = W.levN T c ζ x k := by
  rw [levN_eq_serMul, lev_letE, serMul_one]

theorem Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  show (W.φA ^ (W.s - 1)) W.q = W.q
  rw [hs, Nat.sub_self, pow_zero]
  rfl

theorem levQ_pt (hs : W.s = 1) (i : ZMod n) (ζ : LL) (hζ : ζ ^ PD.p = 1) (hζ1 : ζ ≠ 1) :
    PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev i ζ W.Q) ≠ 0 := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hprim : IsPrimitiveRoot ζ (PD.p ^ 1) := by
    have h := IsPrimitiveRoot.orderOf ζ
    rw [orderOf_eq_prime hζ hζ1] at h
    rwa [pow_one]
  obtain ⟨E, hE0, hED, hE⟩ := W.lev_π i ζ ⟨1, hprim⟩
  have hprod : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext j
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ,
      LocWach.q]
    exact W.q₀_def
  have hl := congrArg (W.lev i ζ) hprod
  rw [map_mul, map_sub, map_pow, map_add, map_one, hE] at hl
  rw [Q_eq_q W hs]
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have := W.v_l
    rw [h, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  have ha0 : PowerSeries.constantCoeff (W.lev i ζ letπ) = ζ - 1 := by
    have h := congrArg PowerSeries.constantCoeff hE
    rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at h
    linear_combination h
  have hz : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hc0 : PowerSeries.constantCoeff (W.lev i ζ W.q) = 0 := by
    have h := congrArg PowerSeries.constantCoeff hl
    rw [map_mul, map_sub, map_one, map_pow, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one,
      hζ, sub_self, ha0] at h
    exact (mul_eq_zero.1 h).resolve_left hz
  refine ⟨hc0, ?_⟩
  obtain ⟨b', hb'⟩ := PowerSeries.X_dvd_iff.2 hc0
  have hEp : PowerSeries.coeff 1 (E ^ PD.p) = (PD.p : LL) := by
    have hd : PowerSeries.derivative LL (E ^ PD.p) = (PD.p : LL) • E ^ PD.p := by
      rw [Derivation.leibniz_pow, hED, smul_eq_mul, ← pow_succ, Nat.sub_add_cancel PD.hp.one_lt.le,
        Nat.cast_smul_eq_nsmul]
    have h := congrArg (PowerSeries.coeff 0) hd
    have hc : PowerSeries.coeff 0 (E ^ PD.p) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hE0, one_pow]
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, hc] at h
    simpa using h
  have h1 := congrArg (PowerSeries.coeff 1) hl
  rw [hb', mul_left_comm, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, ha0, mul_pow, ← map_pow, hζ, map_one, one_mul, map_sub, hEp, PowerSeries.coeff_one,
    if_neg one_ne_zero, sub_zero] at h1
  rw [hb', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  intro h0
  rw [h0, mul_zero] at h1
  exact hp0 h1.symm

end Lev

end Formalism.MainNotions.N.Ln34.ModelFPf

end

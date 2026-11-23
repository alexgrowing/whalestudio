import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne
import Formalism.LogVandermondeBounds.LogVandermondeProofs.TaylorLogMetric

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset Formalism.LogVandermondeBounds.TaylorLogMetric

theorem normalised_equation_general : EqNormalisedGeneral := by
  unfold EqNormalisedGeneral
  intro E _ _ Ψ A _ ι χ G G' Γ Γ' _ _ _ _ j j' dt dt' dr dr' V _ _ pull Th M M' hj hj' hχ hpull
    a b γ γ' g g'
  have hinv : ∀ u : unitary E, ∏ τ ∈ Ψ, τ (star (u : E)) = (∏ τ ∈ Ψ, τ (u : E))⁻¹ := by
    intro u
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Unitary.coe_star_mul_self u, map_one]
  have hne : ∀ u : unitary E, (∏ τ ∈ Ψ, τ (u : E)) ≠ 0 := by
    intro u
    rw [Finset.prod_ne_zero_iff]
    intro τ _ h
    have := congrArg τ (Unitary.coe_star_mul_self u)
    rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  have hχg : ((χ (dt (j γ)) : ℂˣ) : ℂ) = (∏ τ ∈ Ψ, τ ((dr γ : unitary E) : E))⁻¹ := by
    rw [hj, hχ, Finset.prod_inv_distrib]
  have hχg' : ((χ (dt' (j' γ')) : ℂˣ) : ℂ) = (∏ τ ∈ Ψ, τ ((dr' γ' : unitary E) : E))⁻¹ := by
    rw [hj', hχ, Finset.prod_inv_distrib]
  have hP := hne (dr γ)
  have hP' := hne (dr' γ')
  rw [LinearMap.map_smul, hpull, smul_smul, smul_smul]
  congr 1
  simp only [map_mul, Units.val_mul, Units.val_zpow_eq_zpow_val, mul_zpow, hχg, hχg', hinv]
  generalize (∏ τ ∈ Ψ, τ ((dr γ : unitary E) : E)) = P at hP ⊢
  generalize (∏ τ ∈ Ψ, τ ((dr' γ' : unitary E) : E)) = P' at hP' ⊢
  rw [zpow_sub₀ hP, zpow_add₀ hP', zpow_natCast, zpow_natCast, inv_zpow, inv_zpow, inv_pow]
  field_simp

theorem normalised_equation : EqNormalised := by
  unfold EqNormalised
  intro E _ _ Ψ A _ ι χ G G' Γ Γ' _ _ _ _ j j' dt dt' dr dr' V _ _ pull Th M M' h1 h2 h3 h4
    γ γ' g g'
  have := normalised_equation_general E Ψ A ι χ G G' Γ Γ' j j' dt dt' dr dr' V pull Th M M'
    h1 h2 h3 h4 (M' : ℤ) (-(M : ℤ)) γ γ' g g'
  rw [this]
  simp

private theorem orbit_even_card_half_filter_zero {α : Type} (φ c : Equiv.Perm α) (κ : α → ZMod 2) (O : Finset α)
    {inst : DecidablePred (fun τ => κ τ = 0)} {deq : DecidableEq α}
    (hφ : ∀ τ, κ (φ τ) = κ τ + 1) (hc : ∀ τ, κ (c τ) = κ τ + 1) (hO : ∀ τ, φ τ ∈ O ↔ τ ∈ O) :
    Even O.card ∧ 2 * (O.filter (fun τ => κ τ = 0)).card = O.card ∧
      2 * ((O.image c).filter (fun τ => κ τ = 0)).card = O.card := by
  have h1 : (O.filter (fun τ => κ τ = 0)).card = (O.filter (fun τ => ¬ κ τ = 0)).card := by
    apply Finset.card_nbij' (fun τ => φ τ) (fun τ => φ.symm τ)
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter] at hτ ⊢
      refine ⟨(hO τ).2 hτ.1, ?_⟩
      rw [hφ, hτ.2]
      decide
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter] at hτ ⊢
      have e := hφ (φ.symm τ)
      rw [Equiv.apply_symm_apply] at e
      refine ⟨(hO _).1 (by rw [Equiv.apply_symm_apply]; exact hτ.1), ?_⟩
      have h2 := hτ.2
      generalize κ (φ.symm τ) = y at e ⊢
      generalize κ τ = x at e h2
      revert x y
      decide
    · intro τ _
      simp
    · intro τ _
      simp
  have h3 := Finset.card_filter_add_card_filter_not (s := O) (fun τ => κ τ = 0)
  have h4 : ((O.image c).filter (fun τ => κ τ = 0)).card
      = (O.filter (fun τ => ¬ κ τ = 0)).card := by
    symm
    apply Finset.card_nbij' (fun τ => c τ) (fun τ => c.symm τ)
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hτ ⊢
      refine ⟨⟨τ, hτ.1, rfl⟩, ?_⟩
      have h2 := hτ.2
      rw [hc]
      generalize κ τ = x at h2 ⊢
      revert x
      decide
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hτ ⊢
      obtain ⟨⟨a, ha, rfl⟩, h2⟩ := hτ
      rw [Equiv.symm_apply_apply]
      refine ⟨ha, ?_⟩
      rw [hc] at h2
      generalize κ a = x at h2 ⊢
      revert x
      decide
    · intro τ _
      simp
    · intro τ _
      simp
  exact ⟨⟨(O.filter (fun τ => κ τ = 0)).card, by omega⟩, by omega, by omega⟩

theorem half_orbit_count : OrbitHalf := by
  unfold OrbitHalf
  intro Emb _ φ c κ τ₀ hφ hc
  exact orbit_even_card_half_filter_zero φ c κ _ hφ hc
    (fun τ => by simp [Finset.mem_filter, Equiv.Perm.sameCycle_apply_right])

private theorem sum_filter_val_eq_zero_of_balanced_sign_split {α : Type} [Fintype α] [DecidableEq α] (p : α → Prop)
    {inst : DecidablePred p} (O C : Finset α) (e : ℤ) (val : α → ℤ) (hdisj : Disjoint O C)
    (hO : ∀ τ ∈ O, val τ = e) (hC : ∀ τ ∈ C, val τ = -e)
    (hR : ∀ τ, τ ∉ O → τ ∉ C → val τ = 0)
    (h2 : 2 * (O.filter p).card = O.card) (h3 : 2 * (C.filter p).card = O.card) :
    ∑ τ ∈ univ.filter p, val τ = 0 := by
  have key : ∀ τ, val τ = (if τ ∈ O then e else 0) + (if τ ∈ C then -e else 0) := by
    intro τ
    by_cases h1 : τ ∈ O
    · have h1' : τ ∉ C := Finset.disjoint_left.1 hdisj h1
      simp [h1, h1', hO τ h1]
    · by_cases h1' : τ ∈ C
      · simp [h1, h1', hC τ h1']
      · simp [h1, h1', hR τ h1 h1']
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.sum_ite_mem, Finset.sum_const, Finset.sum_const]
  have hA : (univ.filter p ∩ O).card = (O.filter p).card := by
    congr 1
    ext τ
    simp [and_comm]
  have hB : (univ.filter p ∩ C).card = (C.filter p).card := by
    congr 1
    ext τ
    simp [and_comm]
  rw [hA, hB, show (O.filter p).card = (C.filter p).card by omega]
  simp

theorem character_unit_split_or_inert : ChiUnitSplitInert := by
  unfold ChiUnitSplitInert
  intro Emb _ φ c κ τ₀ hφ hc hdisj e val hO hC hR
  classical
  obtain ⟨-, h2, h3⟩ := half_orbit_count Emb φ c κ τ₀ hφ hc
  exact sum_filter_val_eq_zero_of_balanced_sign_split _ _ _ e val hdisj hO hC hR h2 h3

theorem lift_of_types : LiftTypes := by
  unfold LiftTypes
  intro U A _ _ ι n χ m e M M' hχ hm
  have hz : ∀ (f : A →* ℂˣ) (k : ℤ) (x : A), (f ^ k) x = (f x) ^ k := fun _ _ _ => rfl
  refine ⟨fun z => ?_, fun z => ?_, fun lam lam' ν h1 h2 => by omega⟩
  · have h1 : (m * χ ^ (-M')) (ι z) = χ (ι z) ^ (e - M') := by
      rw [MonoidHom.mul_apply, hz, hm]
      group
    refine ⟨h1, ?_⟩
    rw [h1, hχ]
    group
  · have h1 : (m⁻¹ * χ ^ M) (ι z) = χ (ι z) ^ (-(e - M)) := by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hz, hm]
      group
    refine ⟨h1, ?_⟩
    rw [h1, hχ]
    group

theorem type_under_twist : TypeTwist := by
  intro K _ τ q hq ε η π hε hη hπ h lam
  simp only [map_mul, MvPowerSeries.map_C, MvPowerSeries.expand_C, map_inv₀, h]
  rw [mul_sub, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  congr 3
  field_simp

theorem power_of_unit_formula : EpsPow := by
  unfold EpsPow
  intro A _ q ε η h1 h2 l
  induction l with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, mul_pow, ← pow_mul, mul_comm k q, pow_mul, h2, h1]
    ring

theorem sign_of_local_symbol : SeSign := by
  unfold SeSign
  intro A _ q ε η hq h1 h2 n ζ e L
  have hηq : η ^ q = η := by
    obtain ⟨k, rfl⟩ := hq
    rw [pow_succ, pow_mul, sq, h2, one_pow, one_mul]
  have hε := power_of_unit_formula A q ε η h1 hηq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hηl : η ^ l * η ^ l = 1 := by rw [← mul_pow, h2, one_pow]
  rw [mul_pow, hε l, neg_pow]
  linear_combination ((-1) ^ l * ε * ζ (e - 2 * (l : ZMod n)) ^ q ^ l) * hηl

theorem inverse_of_local_symbol : SeInverse := by
  unfold SeInverse
  intro A _ p _ _ n ζ e L
  haveI : ExpChar A p := ExpChar.prime (Fact.out)
  rw [show ∀ x : A, x ^ p ^ 2 = iterateFrobenius A p 2 x from
    fun x => by rw [iterateFrobenius_def]]
  rw [map_sum, Finset.sum_range_succ']
  simp only [map_mul, map_pow, map_neg, map_one, iterateFrobenius_def]
  have hidx : ∀ l : ℕ, e - 2 * ((l + 1 : ℕ) : ZMod n) = e - 2 - 2 * (l : ZMod n) := by
    intro l
    push_cast
    ring
  simp only [hidx]
  rw [add_right_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero (fun l _ => by ring)]
  simp

theorem uniformizer_logarithm : VarpiLog := by
  unfold VarpiLog
  intro R _ p q ϖ hq h
  have hϖq : ϖ ^ q = (p : R) * ϖ := by
    rw [← h, ← pow_succ]
    congr 1
    omega
  refine ⟨fun e => ?_, fun e he => ?_⟩
  · induction e with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih, mul_pow, hϖq, Finset.sum_range_succ', ← pow_mul]
      have hs : ∑ i ∈ range k, q ^ (i + 1) = q * ∑ i ∈ range k, q ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => pow_succ' q i)
      rw [hs]
      ring
  · induction e, he using Nat.le_induction with
    | base =>
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp only [pow_zero, pow_one]
      omega
    | succ k hk ih =>
      rw [Finset.sum_range_succ]
      have : 0 < q ^ k := pow_pos (by omega) k
      omega

theorem gamma_factor_functional_equation : GcFunEq := by
  intro K _ _ σ c p hp hc a b
  obtain ⟨_, h⟩ := logarithm_series_coefficient_identities p hp
  have h1 := congrArg (Rat.cast : ℚ → K) (h a b)
  have h2 := congrArg (Rat.cast : ℚ → K) (h b a)
  have hB : ∀ x y, coefB p x y = coefA p y x := fun _ _ => rfl
  by_cases hab : p ∣ a ∧ p ∣ b
  · have hba : p ∣ b ∧ p ∣ a := ⟨hab.2, hab.1⟩
    rw [if_pos hab] at h1 ⊢
    rw [if_pos hba] at h2
    push_cast at h1 h2
    rw [hB (a / p) (b / p), h1, h2, hc]
    simp only [hB]
    ring
  · have hba : ¬ (p ∣ b ∧ p ∣ a) := fun h => hab ⟨h.2, h.1⟩
    rw [if_neg hab] at h1 ⊢
    rw [if_neg hba] at h2
    push_cast at h1 h2
    rw [hB] at h1 h2 ⊢
    linear_combination (σ c) * h1 - c * h2

theorem no_form_of_bidegree_one_one : PowerCongruenceIffEqual := by
  unfold PowerCongruenceIffEqual
  intro l d s s' hl hs hs' hdiv
  have h1 : l ^ s < l ^ d := Nat.pow_lt_pow_right (by omega) hs
  have h2 : l ^ s' < l ^ d := Nat.pow_lt_pow_right (by omega) hs'
  have h3 : 1 ≤ l ^ s := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ l ^ s' := Nat.one_le_pow _ _ (by omega)
  have h5 : 1 ≤ l ^ d := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h5, Nat.cast_pow, Nat.cast_one] at hdiv
  have h1' : (l : ℤ) ^ s < (l : ℤ) ^ d := by exact_mod_cast h1
  have h2' : (l : ℤ) ^ s' < (l : ℤ) ^ d := by exact_mod_cast h2
  have h3' : (1 : ℤ) ≤ (l : ℤ) ^ s := by exact_mod_cast h3
  have h4' : (1 : ℤ) ≤ (l : ℤ) ^ s' := by exact_mod_cast h4
  have hz := Int.eq_zero_of_abs_lt_dvd hdiv (by rw [abs_lt]; constructor <;> linarith)
  have h6 : (l : ℤ) ^ s = (l : ℤ) ^ s' := by linarith
  have h7 : l ^ s = l ^ s' := by exact_mod_cast h6
  exact Nat.pow_right_injective hl h7

theorem averaging_projector : AverageProjector := by
  unfold AverageProjector
  intro K _ N ζ hN hζ w
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd w).2 h]
    simp
  · have hne : ζ ^ w ≠ 1 := fun h' => h ((hζ.zpow_eq_one_iff_dvd w).1 h')
    rw [geom_sum_eq hne]
    have h1 : (ζ ^ w) ^ N = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [h1, sub_self, zero_div]

theorem sum_of_two_units : SumTwoUnits := by
  unfold SumTwoUnits
  intro R _ _ ⟨x, y, z, hxy, hyz, hxz⟩ a
  have key : ∃ t : IsLocalRing.ResidueField R, t ≠ 0 ∧ t ≠ IsLocalRing.residue R a := by
    by_contra hcon
    push_neg at hcon
    have h : ∀ t, t = 0 ∨ t = IsLocalRing.residue R a := fun t => by
      by_cases ht : t = 0
      · exact Or.inl ht
      · exact Or.inr (hcon t ht)
    rcases h x with hx | hx <;> rcases h y with hy | hy <;> rcases h z with hz | hz <;> simp_all
  obtain ⟨t, ht0, hta⟩ := key
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective t
  have hu : IsUnit u := by rwa [← IsLocalRing.residue_ne_zero_iff_isUnit]
  have hv : IsUnit (a - u) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub]
    exact sub_ne_zero.2 (Ne.symm hta)
  exact ⟨hu.unit, hv.unit, by simp⟩

theorem cube_elimination : CubeEliminate := by
  unfold CubeEliminate
  intro M Q _ _ φ hpar hcube
  have hi : ∀ a b c, φ (a + b + c) - φ (a + b) - φ (b + c) - φ (c + a) + φ a + φ b + φ c = 0 := by
    intro a b c
    calc φ (a + b + c) - φ (a + b) - φ (b + c) - φ (c + a) + φ a + φ b + φ c
        = (φ (a + b + c) + φ (a - b) + φ (b - c) + φ (c - a)) - (φ (a + b) + φ (a - b))
            - (φ (b + c) + φ (b - c)) - (φ (c + a) + φ (c - a)) + φ a + φ b + φ c := by abel
      _ = 3 • (φ a + φ b + φ c) - (2 • φ a + 2 • φ b) - (2 • φ b + 2 • φ c)
            - (2 • φ c + 2 • φ a) + φ a + φ b + φ c := by
          rw [hcube, hpar a b, hpar b c, hpar c a]
      _ = 0 := by abel
  refine ⟨hi, fun a a' b => ?_⟩
  simp only [cob]
  have := hi a a' b
  rw [add_comm b a] at this
  rw [← sub_eq_zero, ← this]
  abel

theorem tilde_adjoint_formula : TildeAdjoint := by
  unfold TildeAdjoint
  intro O M Q _ _ _ _ _ β hl hr hs ι _ a x y
  have hL : ∀ (s : Finset ι) (f : ι → M) (b : M), β (∑ i ∈ s, f i) b = ∑ i ∈ s, β (f i) b :=
    fun s f b => map_sum (AddMonoidHom.mk' (fun u => β u b) (fun u v => hl u v b)) f s
  have hR : ∀ (s : Finset ι) (f : ι → M) (u : M), β u (∑ i ∈ s, f i) = ∑ i ∈ s, β u (f i) :=
    fun s f u => map_sum (AddMonoidHom.mk' (fun v => β u v) (fun v w => hr u v w)) f s
  simp only [hL, hR, hs]
  exact Finset.sum_comm

theorem parallelogram_law_zero : ParallelogramZero := by
  unfold ParallelogramZero
  intro T _ _ m h h0 Q
  by_cases hQ : Q = 0
  · rw [hQ, h0]
  have hsum := Finset.sum_congr rfl (fun P (_ : P ∈ (univ : Finset T)) => h P Q hQ)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have e1 : ∑ P, m (P + Q) = ∑ P, m P := Fintype.sum_equiv (Equiv.addRight Q) _ _ (fun _ => rfl)
  have e2 : ∑ P, m (P - Q) = ∑ P, m P := Fintype.sum_equiv (Equiv.subRight Q) _ _ (fun _ => rfl)
  have e3 : ∑ P, 2 * m P = 2 * ∑ P, m P := by rw [Finset.mul_sum]
  rw [e1, e2, e3] at hsum
  have hc : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have h4 : (Fintype.card T : ℝ) * (2 * m Q) = 0 := by linarith
  rcases mul_eq_zero.1 h4 with h5 | h5
  · linarith
  · linarith

theorem bimultiplicative_divisible_torsion : BimultDivisibleTorsion := by
  unfold BimultDivisibleTorsion
  intro B H _ _ htor hdiv
  refine ⟨fun z hz1 hz2 a b => ?_, fun c hc hneg a => ?_⟩
  · have hz0 : z 0 b = 1 := by
      have := hz1 0 0 b
      rw [add_zero] at this
      exact mul_left_cancel (this.symm.trans (mul_one _).symm)
    obtain ⟨n, hn, hnb⟩ := htor b
    obtain ⟨a', rfl⟩ := hdiv a n hn
    have hz0' : z a' 0 = 1 := by
      have := hz2 a' 0 0
      rw [add_zero] at this
      exact mul_left_cancel (this.symm.trans (mul_one _).symm)
    have h1 : ∀ k : ℕ, z (k • a') b = z a' b ^ k := by
      intro k
      induction k with
      | zero => rw [zero_smul, pow_zero, hz0]
      | succ k ih => rw [succ_nsmul, hz1, ih, pow_succ]
    have h2 : ∀ k : ℕ, z a' (k • b) = z a' b ^ k := by
      intro k
      induction k with
      | zero => rw [zero_smul, pow_zero, hz0']
      | succ k ih => rw [succ_nsmul, hz2, ih, pow_succ]
    rw [h1, ← h2, hnb, hz0']
  · have hc0 : c 0 = 1 := by
      have := hc 0 0
      rw [add_zero] at this
      exact mul_left_cancel (this.symm.trans (mul_one _).symm)
    have hsq : ∀ x, c x * c x = 1 := by
      intro x
      have := hc x (-x)
      rw [add_neg_cancel, hc0, hneg] at this
      exact this.symm
    obtain ⟨a', rfl⟩ := hdiv a 2 (by norm_num)
    rw [two_nsmul, hc, hsq]

theorem teichmuller_frobenius_fixed : TeichFrobenius := by
  unfold TeichFrobenius
  intro p _ k _ _ x s
  have key : ∀ y : k, WittVector.frobenius (WittVector.teichmuller p y)
      = WittVector.teichmuller p (y ^ p) := by
    intro y
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]
  suffices h : (WittVector.frobenius)^[s] (WittVector.teichmuller p x)
      = WittVector.teichmuller p (x ^ p ^ s) by
    rw [h, map_pow]
  induction s with
  | zero => simp
  | succ s ih => rw [Function.iterate_succ_apply', ih, key, ← pow_mul, ← pow_succ]

theorem kronecker_symbol_comparison : KroneckerCompare := by
  unfold KroneckerCompare
  intro h w d γ L1 L1' S hh hw hd hL1 heq
  have hr : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hl1 : Real.log (2 / Real.sqrt d) = Real.log 2 - Real.log (Real.sqrt d) :=
    Real.log_div (by norm_num) hr.ne'
  have hl2 : Real.log (2 * Real.sqrt d) = Real.log 2 + Real.log (Real.sqrt d) :=
    Real.log_mul (by norm_num) hr.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hh' : h ≠ 0 := hh.ne'
  have hw' : w ≠ 0 := hw.ne'
  have hr' : Real.sqrt d ≠ 0 := hr.ne'
  subst hL1
  rw [hl1] at heq
  rw [hl2]
  have heq2 : L1' = γ * (2 * Real.pi * h / (w * Real.sqrt d))
      - 2 * Real.pi * h / (w * Real.sqrt d) * (Real.log 2 + Real.log (Real.sqrt d))
      - 2 * Real.pi * S / (w * Real.sqrt d) := by
    have h5 : L1' = (2 / (w * Real.sqrt d)) * (Real.pi * h * (Real.log 2 - Real.log (Real.sqrt d))
        + 2 * Real.pi * (h * (γ - Real.log 2) - S / 2))
        - γ * (2 * Real.pi * h / (w * Real.sqrt d)) := by linarith
    rw [h5]
    field_simp
    ring
  rw [heq2]
  field_simp
  ring

theorem periodic_arithmetic : PerArithmetic := by
  unfold PerArithmetic
  intro d v γ Λ mη hd hv hm
  have hr : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hπ := Real.pi_pos
  have e1 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) hπ.ne', show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have e2 : Real.log (2 * Real.sqrt d) = Real.log 2 + Real.log (Real.sqrt d) :=
    Real.log_mul (by norm_num) hr.ne'
  have e3 : Real.log (2 * Real.pi / Real.sqrt d)
      = Real.log 2 + Real.log Real.pi - Real.log (Real.sqrt d) := by
    rw [Real.log_div (mul_pos two_pos hπ).ne' hr.ne', Real.log_mul (by norm_num) hπ.ne']
  have e4 : Real.log (2 * v / Real.sqrt d) = Real.log 2 + Real.log v - Real.log (Real.sqrt d) := by
    rw [Real.log_div (mul_pos two_pos hv).ne' hr.ne', Real.log_mul (by norm_num) hv.ne']
  have e5 : Real.log (Real.pi / v) = Real.log Real.pi - Real.log v := Real.log_div hπ.ne' hv.ne'
  refine ⟨?_, ?_⟩
  · rw [hm, e1, e2, e3]
    ring
  · rw [hm, e1, e2, e4, e5]
    ring

theorem cayley_transform_skew : CayleySkew := by
  unfold CayleySkew
  intro E V _ _ _ h g θ hadd hherm hg hθ y y'
  have hsub1 : ∀ x x' z, h (x - x') z = h x z - h x' z := fun x x' z => by
    have := hadd (x - x') x' z
    rw [sub_add_cancel] at this
    exact eq_sub_of_add_eq this.symm
  have hsub2 : ∀ z x x', h z (x - x') = h z x - h z x' := fun z x x' => by
    rw [hherm z (x - x'), hsub1, star_sub, ← hherm, ← hherm]
  have h1 : h y (y' - g y') + h (y - g y) y' = h (y - g y) (y' - g y') := by
    simp only [hsub1, hsub2, hg]
    ring
  refine ⟨h1, ?_⟩
  rw [star_sub, star_mul, ← hherm, ← hherm]
  have hθ' : star θ = 1 - θ := by
    rw [← hθ]
    ring
  rw [hθ']
  linear_combination h1

theorem norm_conjugation_invariant : NormConjInvariant := by
  unfold NormConjInvariant
  intro s q r hq hr X _ Φ hΦ
  have hsr : ‖s r‖ = ‖r‖ := by
    have h1 : (s r) ^ 2 = (q : ℂ) := by rw [← map_pow, hr, map_natCast]
    have h2 : ‖s r‖ ^ 2 = ‖r‖ ^ 2 := by rw [← norm_pow, ← norm_pow, h1, hr]
    rw [← Real.sqrt_sq (norm_nonneg (s r)), h2, Real.sqrt_sq (norm_nonneg r)]
  have hroot : ∀ (z : ℂ) (n : ℕ), 0 < n → z ^ n = 1 → ‖z‖ = 1 := fun z n hn hz => by
    have : ‖z‖ ^ n = 1 := by rw [← norm_pow, hz, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 this
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  rcases hΦ x with h0 | ⟨ζ, n, k, hn, hζ, hx⟩
  · rw [h0, map_zero]
  · rw [hx, map_mul, map_zpow₀, norm_mul, norm_mul, norm_zpow, norm_zpow, hsr,
      hroot ζ n hn hζ, hroot (s ζ) n hn (by rw [← map_pow, hζ, map_one])]

end Formalism.HermitianLattices.IntegralLatticeDensity

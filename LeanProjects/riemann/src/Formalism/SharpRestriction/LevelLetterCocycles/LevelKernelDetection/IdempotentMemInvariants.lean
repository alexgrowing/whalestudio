import Formalism.SharpRestriction.LevelLetterCocycles.CoordStepsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

variable (W) in

def k17e (i : ZMod n) : W.EE := algebraMap (LetA O n) W.EE (letE i)

theorem idempotent_mul_self_bis (i : ZMod n) : k17e W i * k17e W i = k17e W i := by
  rw [k17e, ← map_mul, letE_mul_self]

theorem idempotent_gamma_invariant (i : ZMod n) (g : W.Gam) : W.γE g (k17e W i) = k17e W i := by
  rw [k17e, W.γE_ext]
  exact congrArg (algebraMap (LetA O n) W.EE) (γA_letE W g i)

theorem idempotent_smul_eq_mul (i : ZMod n) (ε : W.EE) : (letE i : LetA O n) • ε = k17e W i * ε :=
  Algebra.smul_def _ _

theorem isUnit_of_isUnit_mod_l (x : W.EE)
    (h : IsUnit (Ideal.Quotient.mk (Ideal.span {((PD.p : ℕ) : W.EE)}) x)) : IsUnit x := by
  have hc := W.EE_complete
  obtain ⟨u, hu⟩ := h
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : W.EE ⧸ Ideal.span {((PD.p : ℕ) : W.EE)})
  have h1 : x * w - 1 ∈ Ideal.span {((PD.p : ℕ) : W.EE)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, ← hu, Units.mul_inv, map_one,
      sub_self]
  have h2 := Ideal.isUnit_of_sub_one_mem_jacobson_bot _
    (IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}) h1)
  exact isUnit_of_mul_isUnit_left h2

theorem isUnit_of_unit_coefficient (hOloc : IsLocalRing O)
    (hOnil : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d)
    (i : ZMod n) (x : W.EE) (hx : k17e W i * x = x) (m : ℕ) (a : LetA O n)
    (ha : x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a ∈
      Ideal.span {((PD.p : ℕ) : W.EE) ^ 1})
    (hk : ∃ k, IsUnit (PowerSeries.coeff k (a i))) : IsUnit (x + (1 - k17e W i)) := by
  classical
  set k₀ := Nat.find hk with hk₀
  have hu₀ : IsUnit (PowerSeries.coeff k₀ (a i)) := Nat.find_spec hk
  have hlow : ∀ j < k₀, PowerSeries.coeff j (a i) ∈ IsLocalRing.maximalIdeal O := fun j hj =>
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (Nat.find_min hk hj))
  obtain ⟨Lp, hLp⟩ : ∃ Lp : PowerSeries O, Lp = ∑ j ∈ Finset.range k₀,
    PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j := ⟨_, rfl⟩
  have hcL : ∀ d, PowerSeries.coeff d Lp = if d < k₀ then PowerSeries.coeff d (a i) else 0 := by
    intro d
    simp only [hLp, map_sum, PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have hdvd : (PowerSeries.X : PowerSeries O) ^ k₀ ∣ a i - Lp := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    rw [map_sub, hcL, if_pos hd, sub_self]
  obtain ⟨U, hU⟩ := hdvd
  have hUu : IsUnit U := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h1 := congrArg (PowerSeries.coeff k₀) hU
    rw [PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, map_sub, hcL,
      if_neg (lt_irrefl _), sub_zero] at h1
    rw [← h1]
    exact hu₀
  let δf : LetA O n := fun j => if j = i then 1 else PowerSeries.X ^ k₀
  let uf : LetA O n := fun j => if j = i then U else 1
  let γf : LetA O n := fun j => if j = i then PowerSeries.X ^ k₀ * U else 1
  have hγδ : γf * δf = letπ ^ k₀ * uf := by
    funext j
    by_cases h : j = i
    · simp [γf, δf, uf, letπ, h, mul_comm]
    · simp [γf, δf, uf, letπ, h]
  have huf : IsUnit uf := Pi.isUnit_iff.2 fun j => by
    by_cases h : j = i
    · simp [uf, h, hUu]
    · simp [uf, h]
  have hγ : IsUnit (algebraMap (LetA O n) W.EE γf) := by
    have h1 : IsUnit (algebraMap (LetA O n) W.EE (γf * δf)) := by
      rw [hγδ, map_mul, map_pow]
      exact (W.EE_π.pow _).mul (huf.map _)
    rw [map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  let t : ℕ → LetA O n := fun j =>
    Pi.single i (PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j)
  have hdec : (letE i : LetA O n) * a + (1 - letE i) = ∑ j ∈ Finset.range k₀, t j + γf := by
    funext j'
    by_cases h : j' = i
    · rw [h]
      have hsum : (∑ j ∈ Finset.range k₀, t j) i = Lp := by
        rw [hLp, Finset.sum_apply]
        simp [t]
      have hai : a i = Lp + PowerSeries.X ^ k₀ * U := by rw [← hU]; ring
      rw [show (∑ j ∈ Finset.range k₀, t j + γf) i = (∑ j ∈ Finset.range k₀, t j) i + γf i from rfl,
        hsum]
      simp [letE, γf, hai]
    · simp [t, γf, letE, Finset.sum_apply, h]
  set I := Ideal.span {((PD.p : ℕ) : W.EE)} with hI
  have hnil : ∀ j ∈ Finset.range k₀,
      IsNilpotent (Ideal.Quotient.mk I (algebraMap (LetA O n) W.EE (t j))) := by
    intro j hj
    obtain ⟨N, d, hNd⟩ := hOnil _ (hlow j (Finset.mem_range.1 hj))
    refine ⟨N + 1, ?_⟩
    have hpow : t j ^ (N + 1) = ((PD.p : ℕ) : LetA O n) *
        Pi.single i (PowerSeries.C (PowerSeries.coeff j (a i) * d) * PowerSeries.X ^ (j * (N + 1))) := by
      funext j'
      by_cases h : j' = i
      · subst h
        simp only [t, Pi.pow_apply, Pi.mul_apply, Pi.single_eq_same, Pi.natCast_apply]
        rw [mul_pow, ← map_pow, pow_succ, hNd, ← pow_mul]
        simp only [map_mul, map_natCast]
        ring
      · simp [t, h]
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, hpow, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hq : Ideal.Quotient.mk I (x * algebraMap (LetA O n) W.EE (letπ ^ m) + (1 - k17e W i)) =
      Ideal.Quotient.mk I (algebraMap (LetA O n) W.EE ((letE i : LetA O n) * a + (1 - letE i))) := by
    rw [Ideal.Quotient.eq]
    have h1 : x * algebraMap (LetA O n) W.EE (letπ ^ m) + (1 - k17e W i) -
        algebraMap (LetA O n) W.EE ((letE i : LetA O n) * a + (1 - letE i)) =
        k17e W i * (x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a) := by
      rw [map_add, map_mul, map_sub, map_one]
      simp only [k17e] at hx ⊢
      linear_combination (-(algebraMap (LetA O n) W.EE (letπ ^ m))) * hx
    rw [h1, hI, ← pow_one ((PD.p : ℕ) : W.EE)]
    exact Ideal.mul_mem_left _ _ ha
  have hunit : IsUnit (x * algebraMap (LetA O n) W.EE (letπ ^ m) + (1 - k17e W i)) := by
    apply isUnit_of_isUnit_mod_l
    rw [hq, hdec, map_add, map_add, map_sum, map_sum]
    exact (isNilpotent_sum hnil).isUnit_add_right_of_commute (hγ.map _) (Commute.all _ _)
  have hprod : (x + (1 - k17e W i)) * (k17e W i * algebraMap (LetA O n) W.EE (letπ ^ m) +
      (1 - k17e W i)) = x * algebraMap (LetA O n) W.EE (letπ ^ m) + (1 - k17e W i) := by
    have he := idempotent_mul_self_bis (W := W) i
    linear_combination (algebraMap (LetA O n) W.EE (letπ ^ m) - 1) * hx -
      (algebraMap (LetA O n) W.EE (letπ ^ m) - 1) * he
  rw [← hprod] at hunit
  exact isUnit_of_mul_isUnit_left hunit

theorem local_corner_unit_dichotomy (hOloc : IsLocalRing O)
    (hOnil : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d)
    (i : ZMod n) (x : W.EE) (hx : k17e W i * x = x) :
    IsUnit (x + (1 - k17e W i)) ∨ IsUnit ((k17e W i - x) + (1 - k17e W i)) := by
  obtain ⟨a, m, ha⟩ := W.EE_dense x 1
  by_cases hk : ∃ k, IsUnit (PowerSeries.coeff k (a i))
  · exact Or.inl (isUnit_of_unit_coefficient hOloc hOnil i x hx m a (by simpa using ha) hk)
  · right
    push Not at hk
    have he := idempotent_mul_self_bis (W := W) i
    refine isUnit_of_unit_coefficient hOloc hOnil i _ (by linear_combination he - hx) m
      ((letE i : LetA O n) * letπ ^ m - a : LetA O n) ?_ ⟨m, ?_⟩
    · have h1 : (k17e W i - x) * algebraMap (LetA O n) W.EE (letπ ^ m) -
          algebraMap (LetA O n) W.EE ((letE i : LetA O n) * letπ ^ m - a) =
          -(x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a) := by
        rw [map_sub, map_mul]
        simp only [k17e]
        ring
      rw [h1]
      exact neg_mem (by simpa using ha)
    · have h1 : ((letE i : LetA O n) * letπ ^ m - a : LetA O n) i = PowerSeries.X ^ m - a i := by
        simp [letE, letπ]
      rw [h1, map_sub, PowerSeries.coeff_X_pow_self]
      have := hOloc
      exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (mem_nonunits_iff.2 (hk m))

variable (W) in

def k17S : Subring W.EE where
  carrier := {ε | ∀ δ ∈ W.DelF, W.γE δ ε = ε}
  mul_mem' {a b} ha hb δ hδ := by rw [map_mul, ha δ hδ, hb δ hδ]
  one_mem' δ _ := map_one _
  add_mem' {a b} ha hb δ hδ := by rw [map_add, ha δ hδ, hb δ hδ]
  zero_mem' δ _ := map_zero _
  neg_mem' {a} ha δ hδ := by rw [map_neg, ha δ hδ]

theorem k17e_mem_k17S (i : ZMod n) : k17e W i ∈ k17S W := fun δ _ => idempotent_gamma_invariant i δ

variable (W) in

def idempotentInvariant (i : ZMod n) : k17S W := ⟨k17e W i, k17e_mem_k17S i⟩

variable (W) in

abbrev k17R (i : ZMod n) : Type := k17S W ⧸ Ideal.span {1 - idempotentInvariant W i}

theorem letterRing_mk_eq (i : ZMod n) {s s' : k17S W}
    (h : Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) s = Ideal.Quotient.mk _ s') :
    k17e W i * (s : W.EE) = k17e W i * s' := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have h1 := congrArg (fun z : k17S W => k17e W i * (z : W.EE)) hc
  simp only [idempotentInvariant, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one] at h1
  have he := idempotent_mul_self_bis (W := W) i
  linear_combination -h1 - (c : W.EE) * he

theorem letterRing_mk_of_eq (i : ZMod n) {s s' : k17S W}
    (h : k17e W i * (s : W.EE) = k17e W i * s') :
    Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) s = Ideal.Quotient.mk _ s' := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  refine ⟨s - s', Subtype.ext ?_⟩
  simp only [idempotentInvariant, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one]
  linear_combination -h

theorem letterRing_isUnit_of (i : ZMod n) (t : k17S W)
    (h : IsUnit (k17e W i * (t : W.EE) + (1 - k17e W i))) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) t) := by
  obtain ⟨u, hu⟩ := h
  have hz : ∀ δ ∈ W.DelF, W.γE δ (u : W.EE) = u := by
    intro δ hδ
    rw [hu, map_add, map_mul, map_sub, map_one, idempotent_gamma_invariant, t.2 δ hδ]
  have hw : ∀ δ ∈ W.DelF, W.γE δ (↑u⁻¹ : W.EE) = ↑u⁻¹ := by
    intro δ hδ
    have h1 : W.γE δ (↑u⁻¹ : W.EE) * u = 1 := by
      conv_lhs => rw [← hz δ hδ]
      rw [← map_mul, Units.inv_mul, map_one]
    calc W.γE δ (↑u⁻¹ : W.EE) = W.γE δ (↑u⁻¹ : W.EE) * (u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]
  let w : k17S W := ⟨↑u⁻¹, hw⟩
  refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ w, ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}))]
  apply letterRing_mk_of_eq
  have h1 : (u : W.EE) * ↑u⁻¹ = 1 := Units.mul_inv u
  rw [hu] at h1
  have he := idempotent_mul_self_bis (W := W) i
  simp only [w, MulMemClass.coe_mul, OneMemClass.coe_one]
  linear_combination (k17e W i) * h1 + ((↑u⁻¹ : W.EE) - (t : W.EE) * ↑u⁻¹) * he

theorem letterRing_isLocalRing (hOloc : IsLocalRing O)
    (hOnil : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d)
    (i : ZMod n) : IsLocalRing (k17R W i) := by
  have : Nontrivial (k17R W i) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    have h1 : (1 : k17S W) ∈ Ideal.span {1 - idempotentInvariant W i} := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 := congrArg (fun z : k17S W => (z : W.EE) * k17e W i) hc
    simp only [idempotentInvariant, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, one_mul] at h2
    have he := idempotent_mul_self_bis (W := W) i
    have h3 : k17e W i = 0 := by linear_combination -h2 - (c : W.EE) * he
    have h4 : (letE i : LetA O n) = 0 := W.EE_inj (by rw [map_zero]; exact h3)
    have h5 := congrFun h4 i
    simp [letE] at h5
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun r => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  have he := idempotent_mul_self_bis (W := W) i
  rcases local_corner_unit_dichotomy hOloc hOnil i (k17e W i * (s : W.EE)) (by rw [← mul_assoc, he]) with h | h
  · exact Or.inl (letterRing_isUnit_of i s h)
  · right
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i})), ← map_sub]
    apply letterRing_isUnit_of i (1 - s)
    convert h using 2
    simp only [AddSubgroupClass.coe_sub, OneMemClass.coe_one]
    ring

def letterRingValueFun (i : ZMod n) (r : k17R W i) : W.EE :=
  k17e W i * ((Ideal.Quotient.mk_surjective r).choose : W.EE)

theorem letterRingValueFun_mk (i : ZMod n) (s : k17S W) :
    letterRingValueFun i (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) s) = k17e W i * s :=
  letterRing_mk_eq i (Ideal.Quotient.mk_surjective _).choose_spec

variable (W) in

def letterRingVal (i : ZMod n) : k17R W i →+ W.EE where
  toFun := letterRingValueFun i
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i})), letterRingValueFun_mk]
    simp
  map_add' r r' := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective r'
    rw [← map_add, letterRingValueFun_mk, letterRingValueFun_mk, letterRingValueFun_mk, AddMemClass.coe_add, mul_add]

theorem letterRing_val_mk (i : ZMod n) (s : k17S W) :
    letterRingVal W i (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) s) = k17e W i * s :=
  letterRingValueFun_mk i s

theorem letterRing_val_mul (i : ZMod n) (r r' : k17R W i) :
    letterRingVal W i (r * r') = letterRingVal W i r * letterRingVal W i r' := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective r'
  rw [← map_mul, letterRing_val_mk, letterRing_val_mk, letterRing_val_mk, MulMemClass.coe_mul]
  have he := idempotent_mul_self_bis (W := W) i
  linear_combination (-(s : W.EE) * s') * he

theorem letterRing_val_one (i : ZMod n) : letterRingVal W i 1 = k17e W i := by
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i})), letterRing_val_mk, OneMemClass.coe_one, mul_one]

theorem letterRing_val_mem (i : ZMod n) (r : k17R W i) : letterRingVal W i r ∈ EEl W i := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [letterRing_val_mk]
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [idempotent_smul_eq_mul, ← mul_assoc, idempotent_mul_self_bis]
  · rw [map_mul, idempotent_gamma_invariant, s.2 δ hδ]

theorem letterRing_val_injective (i : ZMod n) : Function.Injective (letterRingVal W i) := by
  intro r r' h
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective r'
  rw [letterRing_val_mk, letterRing_val_mk] at h
  exact letterRing_mk_of_eq i h

theorem letterRing_val_surjective (i : ZMod n) (ε : W.EE) (hε : ε ∈ EEl W i) : ∃ r, letterRingVal W i r = ε := by
  refine ⟨Ideal.Quotient.mk _ ⟨ε, hε.2⟩, ?_⟩
  rw [letterRing_val_mk]
  have h1 := hε.1
  rw [idempotent_smul_eq_mul] at h1
  exact h1

end Formalism.MainNotions.N.Ln03.Pf

import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section Gen

variable {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V] [Module O V]
  [IsScalarTower O Kf V]

theorem mem_scale {c : Kf} {M : Submodule O V} {x : V} : x ∈ scale c M ↔ ∃ y ∈ M, c • y = x := by
  unfold scale
  exact Submodule.mem_map

theorem scale_one (M : Submodule O V) : scale (1 : Kf) M = M := by
  ext x
  rw [mem_scale]
  simp

end Gen

section Val

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem frac_of_place (v : X.Pl) : IsFractionRing X.G.O X.G.Kf := by
  exact (X.G.P.setting v).frac_O

abbrev piK : X.G.Kf := algebraMap X.G.O X.G.Kf X.vp

theorem piK_ne (hfr : IsFractionRing X.G.O X.G.Kf) : piK X ≠ 0 := by
  haveI := hfr
  intro h
  exact X.unif.ne_zero (IsFractionRing.injective X.G.O X.G.Kf (h.trans (map_zero _).symm))

theorem vsc_def (g : ℝ) : X.vsc g = piK X ^ (⌈g * (X.eO : ℝ)⌉) := rfl

theorem mem_intK {x : X.G.Kf} : x ∈ X.intK ↔ ∃ a : X.G.O, algebraMap X.G.O X.G.Kf a = x := by
  unfold Sys.intK
  exact LinearMap.mem_range

theorem vGeK_iff {x : X.G.Kf} {g : ℝ} :
    X.vGeK x g ↔ ∃ a : X.G.O, X.vsc g * algebraMap X.G.O X.G.Kf a = x := by
  unfold Sys.vGeK
  rw [mem_scale]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_intK X).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, (mem_intK X).2 ⟨a, rfl⟩, rfl⟩

theorem vGeK_of_zpow (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {g : ℝ} {n : ℤ} (a : X.G.O)
    (hn : g * (X.eO : ℝ) ≤ n) (hx : x = piK X ^ n * algebraMap X.G.O X.G.Kf a) : X.vGeK x g := by
  rw [vGeK_iff]
  have hc : ⌈g * (X.eO : ℝ)⌉ ≤ n := Int.ceil_le.mpr hn
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hc)
  refine ⟨X.vp ^ k * a, ?_⟩
  have hn' : n = ⌈g * (X.eO : ℝ)⌉ + k := by omega
  rw [hx, hn', zpow_add₀ (piK_ne X hfr), zpow_natCast, map_mul, map_pow, vsc_def, mul_assoc]

theorem vGeK_zero (g : ℝ) : X.vGeK 0 g := by
  exact (vGeK_iff X).2 ⟨0, by simp⟩

theorem vGeK_add {x y : X.G.Kf} {g : ℝ} (hx : X.vGeK x g) (hy : X.vGeK y g) : X.vGeK (x + y) g := by
  obtain ⟨a, rfl⟩ := (vGeK_iff X).1 hx
  obtain ⟨b, rfl⟩ := (vGeK_iff X).1 hy
  exact (vGeK_iff X).2 ⟨a + b, by rw [map_add, mul_add]⟩

theorem vGeK_sum {ι : Type*} (s : Finset ι) (f : ι → X.G.Kf) {g : ℝ} (h : ∀ i ∈ s, X.vGeK (f i) g) :
    X.vGeK (∑ i ∈ s, f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vGeK_zero X g
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact vGeK_add X (h i (Finset.mem_insert.2 (Or.inl rfl))) (ih fun j hj => h j (Finset.mem_insert.2 (Or.inr hj)))

theorem ceil_mono {g g' : ℝ} (h : g' ≤ g) : ⌈g' * (X.eO : ℝ)⌉ ≤ ⌈g * (X.eO : ℝ)⌉ := by
  exact Int.ceil_mono (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))

theorem vGeK_mono (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {g g' : ℝ} (h : g' ≤ g)
    (hx : X.vGeK x g) : X.vGeK x g' := by
  obtain ⟨a, rfl⟩ := (vGeK_iff X).1 hx
  refine vGeK_of_zpow X hfr (n := ⌈g * (X.eO : ℝ)⌉) a ?_ ?_
  · exact le_trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)) (Int.le_ceil _)
  · rw [vsc_def]

theorem vGeK_mul (hfr : IsFractionRing X.G.O X.G.Kf) {x y : X.G.Kf} {g h : ℝ} (hx : X.vGeK x g)
    (hy : X.vGeK y h) : X.vGeK (x * y) (g + h) := by
  obtain ⟨a, rfl⟩ := (vGeK_iff X).1 hx
  obtain ⟨b, rfl⟩ := (vGeK_iff X).1 hy
  refine vGeK_of_zpow X hfr (n := ⌈g * (X.eO : ℝ)⌉ + ⌈h * (X.eO : ℝ)⌉) (a * b) ?_ ?_
  · push_cast
    rw [add_mul]
    linarith [Int.le_ceil (g * (X.eO : ℝ)), Int.le_ceil (h * (X.eO : ℝ))]
  · rw [vsc_def, vsc_def, zpow_add₀ (piK_ne X hfr), map_mul]
    ring

theorem vGeK_zero_iff {x : X.G.Kf} : X.vGeK x 0 ↔ x ∈ X.intK := by
  rw [vGeK_iff, mem_intK, vsc_def]
  simp

theorem vGeK_one : X.vGeK 1 0 := by
  exact (vGeK_zero_iff X).2 ((mem_intK X).2 ⟨1, map_one _⟩)

theorem vGeK_multiset_prod (hfr : IsFractionRing X.G.O X.G.Kf) {ι : Type*} (f : ι → X.G.Kf) (μ : ℝ)
    (s : Multiset ι) (h : ∀ i ∈ s, X.vGeK (f i) μ) : X.vGeK (s.map f).prod ((Multiset.card s : ℝ) * μ) := by
  induction s using Multiset.induction_on with
  | empty => simpa using vGeK_one X
  | @cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    have h1 := h a (Multiset.mem_cons.2 (Or.inl rfl))
    have h2 := ih (fun i hi => h i (Multiset.mem_cons.2 (Or.inr hi)))
    have e : ((Multiset.card s + 1 : ℕ) : ℝ) * μ = μ + (Multiset.card s : ℝ) * μ := by push_cast; ring
    rw [e]
    exact vGeK_mul X hfr h1 h2

def Rep (x : X.G.Kf) (N : ℤ) : Prop := ∃ u : X.G.Oˣ, x = piK X ^ N * algebraMap X.G.O X.G.Kf (u : X.G.O)

theorem Rep.ne_zero (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {N : ℤ} (h : Rep X x N) : x ≠ 0 := by
  obtain ⟨u, rfl⟩ := h
  exact mul_ne_zero (zpow_ne_zero _ (piK_ne X hfr)) (u.isUnit.map (algebraMap X.G.O X.G.Kf)).ne_zero

theorem Rep.mul (hfr : IsFractionRing X.G.O X.G.Kf) {x y : X.G.Kf} {N N' : ℤ} (hx : Rep X x N) (hy : Rep X y N') :
    Rep X (x * y) (N + N') := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨u', rfl⟩ := hy
  refine ⟨u * u', ?_⟩
  rw [zpow_add₀ (piK_ne X hfr), Units.val_mul, map_mul]
  ring

theorem Rep.inv {x : X.G.Kf} {N : ℤ} (hx : Rep X x N) : Rep X x⁻¹ (-N) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨u⁻¹, ?_⟩
  rw [mul_inv, zpow_neg, map_units_inv]

theorem Rep.one : Rep X 1 0 := by
  exact ⟨1, by simp⟩

theorem Rep.pow (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {N : ℤ} (hx : Rep X x N) (k : ℕ) :
    Rep X (x ^ k) (k * N) := by
  induction k with
  | zero => simpa using Rep.one X
  | succ k ih =>
    rw [pow_succ]
    have e : ((k + 1 : ℕ) : ℤ) * N = (k : ℤ) * N + N := by push_cast; ring
    rw [e]
    exact Rep.mul X hfr ih hx

theorem Rep.zpow (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {N : ℤ} (hx : Rep X x N) (k : ℤ) :
    Rep X (x ^ k) (k * N) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · have := Rep.pow X hfr hx n
    rwa [zpow_natCast]
  · have := Rep.inv X (Rep.pow X hfr hx n)
    rw [zpow_neg, zpow_natCast, neg_mul]
    exact this

theorem Rep.ofP : Rep X (p : X.G.Kf) X.eO := by
  obtain ⟨u, hu⟩ := X.eO_spec
  refine ⟨u⁻¹, ?_⟩
  show (p : X.G.Kf) = algebraMap X.G.O X.G.Kf X.vp ^ (X.eO : ℤ) * algebraMap X.G.O X.G.Kf (↑u⁻¹ : X.G.O)
  rw [zpow_natCast, ← map_pow, ← map_mul, ← hu, mul_assoc, Units.mul_inv, mul_one, map_natCast]

theorem exists_rep (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} (hx : x ≠ 0) : ∃ N, Rep X x N := by
  haveI := hfr
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.G.O) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 X.unif
  obtain ⟨n, u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 X.unif
  refine ⟨(m : ℤ) - n, u * u'⁻¹, ?_⟩
  have hp : algebraMap X.G.O X.G.Kf X.vp ≠ 0 := piK_ne X hfr
  have hu' : algebraMap X.G.O X.G.Kf (u' : X.G.O) ≠ 0 := (u'.isUnit.map _).ne_zero
  dsimp only [piK]
  rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast, Units.val_mul]
  simp only [map_mul, map_pow, map_units_inv]
  first
    | (field_simp; done)
    | (field_simp; ring)

theorem vGeK_iff_of_rep (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {N : ℤ} (hx : Rep X x N) (g : ℝ) :
    X.vGeK x g ↔ g * (X.eO : ℝ) ≤ N := by
  haveI := hfr
  obtain ⟨u, rfl⟩ := hx
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (vGeK_iff X).1 h
    rw [vsc_def] at ha
    by_contra hlt
    push_neg at hlt
    have hc : N < ⌈g * (X.eO : ℝ)⌉ := Int.lt_ceil.mpr hlt
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hc.le)
    have e : ⌈g * (X.eO : ℝ)⌉ = N + k := by omega
    have hk1 : k ≠ 0 := by omega
    rw [e, zpow_add₀ (piK_ne X hfr), zpow_natCast, mul_assoc] at ha
    have ha' := mul_left_cancel₀ (zpow_ne_zero N (piK_ne X hfr)) ha
    have ha'' : algebraMap X.G.O X.G.Kf (X.vp ^ k * a) = algebraMap X.G.O X.G.Kf (u : X.G.O) := by
      rw [map_mul, map_pow]
      exact ha'
    have hO := IsFractionRing.injective X.G.O X.G.Kf ha''
    apply X.unif.not_isUnit
    have hU : IsUnit (X.vp ^ k * a) := by
      rw [hO]
      exact u.isUnit
    exact isUnit_of_dvd_unit (dvd_mul_of_dvd_left (dvd_pow_self _ hk1) a) hU
  · intro h
    exact vGeK_of_zpow X hfr (u : X.G.O) h rfl

theorem vEqK_iff_of_rep (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {N : ℤ} (hx : Rep X x N) (g : ℝ) :
    X.vEqK x g ↔ 0 < X.eO ∧ g * (X.eO : ℝ) = N := by
  unfold Sys.vEqK
  simp only [vGeK_iff_of_rep X hfr hx, not_le]
  constructor
  · rintro ⟨h1, h2⟩
    have he : 0 < X.eO := by
      by_contra h0
      have h00 : X.eO = 0 := by omega
      have h0' : (X.eO : ℝ) = 0 := by exact_mod_cast h00
      have h4 := h2 (g + 1) (by linarith)
      rw [h0', mul_zero] at h4 h1
      linarith
    refine ⟨he, le_antisymm h1 ?_⟩
    have hepos : (0 : ℝ) < X.eO := by exact_mod_cast he
    by_contra hlt
    push_neg at hlt
    have h5 : (N : ℝ) / X.eO * X.eO = N := by field_simp
    linarith [h2 ((N : ℝ) / X.eO) (by rw [lt_div_iff₀ hepos]; exact hlt)]
  · rintro ⟨he, h⟩
    have hepos : (0 : ℝ) < X.eO := by exact_mod_cast he
    refine ⟨h.le, fun g' hg' => ?_⟩
    rw [← h]
    exact mul_lt_mul_of_pos_right hg' hepos

theorem vEqK.ne_zero {x : X.G.Kf} {g : ℝ} (h : X.vEqK x g) : x ≠ 0 := by
  rintro rfl
  have h' := h
  unfold Sys.vEqK at h'
  exact h'.2 (g + 1) (by linarith) (vGeK_zero X _)

theorem vEqK.rep (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {g : ℝ} (h : X.vEqK x g) :
    ∃ N : ℤ, Rep X x N ∧ 0 < X.eO ∧ g * (X.eO : ℝ) = N := by
  obtain ⟨N, hN⟩ := exists_rep X hfr (vEqK.ne_zero X h)
  exact ⟨N, hN, (vEqK_iff_of_rep X hfr hN g).1 h⟩

theorem vEqK_mul (hfr : IsFractionRing X.G.O X.G.Kf) {x y : X.G.Kf} {g h : ℝ} (hx : X.vEqK x g)
    (hy : X.vEqK y h) : X.vEqK (x * y) (g + h) := by
  obtain ⟨N, hN, he, hg⟩ := vEqK.rep X hfr hx
  obtain ⟨N', hN', -, hh⟩ := vEqK.rep X hfr hy
  rw [vEqK_iff_of_rep X hfr (Rep.mul X hfr hN hN')]
  refine ⟨he, ?_⟩
  push_cast
  rw [add_mul, hg, hh]

theorem vEqK_inv (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {g : ℝ} (hx : X.vEqK x g) :
    X.vEqK x⁻¹ (-g) := by
  obtain ⟨N, hN, he, hg⟩ := vEqK.rep X hfr hx
  rw [vEqK_iff_of_rep X hfr (Rep.inv X hN)]
  refine ⟨he, ?_⟩
  push_cast
  rw [neg_mul, hg]

theorem vEqK_one (hfr : IsFractionRing X.G.O X.G.Kf) (he : 0 < X.eO) : X.vEqK 1 0 := by
  exact (vEqK_iff_of_rep X hfr (Rep.one X) 0).2 ⟨he, by simp⟩

theorem vEqK_prod (hfr : IsFractionRing X.G.O X.G.Kf) (he : 0 < X.eO) {ι : Type*} (s : Finset ι)
    (f : ι → X.G.Kf) (g : ι → ℝ) (h : ∀ i ∈ s, X.vEqK (f i) (g i)) : X.vEqK (∏ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vEqK_one X hfr he
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact vEqK_mul X hfr (h i (Finset.mem_insert.2 (Or.inl rfl))) (ih fun j hj => h j (Finset.mem_insert.2 (Or.inr hj)))

theorem vEqK_prod_units (hfr : IsFractionRing X.G.O X.G.Kf) (he : 0 < X.eO) {ι : Type*} (s : Finset ι)
    (f : ι → X.G.Kf) (h : ∀ i ∈ s, X.vEqK (f i) 0) : X.vEqK (∏ i ∈ s, f i) 0 := by
  simpa using vEqK_prod X hfr he s f (fun _ => 0) h

theorem vGeK_ppow (hfr : IsFractionRing X.G.O X.G.Kf) (k : ℤ) : X.vGeK ((p : X.G.Kf) ^ k) (k : ℝ) := by
  rw [vGeK_iff_of_rep X hfr (Rep.zpow X hfr (Rep.ofP X) k)]
  exact_mod_cast le_refl ((k : ℝ) * X.eO)

theorem vEqK_ppow (hfr : IsFractionRing X.G.O X.G.Kf) (he : 0 < X.eO) (k : ℤ) :
    X.vEqK ((p : X.G.Kf) ^ k) (k : ℝ) := by
  refine (vEqK_iff_of_rep X hfr (Rep.zpow X hfr (Rep.ofP X) k) k).2 ⟨he, ?_⟩
  push_cast
  ring

theorem vEqK_zpow (hfr : IsFractionRing X.G.O X.G.Kf) {x : X.G.Kf} {g : ℝ} (hx : X.vEqK x g) (k : ℤ) :
    X.vEqK (x ^ k) (k * g) := by
  obtain ⟨N, hN, he, hg⟩ := vEqK.rep X hfr hx
  rw [vEqK_iff_of_rep X hfr (Rep.zpow X hfr hN k)]
  refine ⟨he, ?_⟩
  push_cast
  rw [mul_assoc, hg]

theorem vGe_iff {j : ℕ} {F : X.Fm j} {g : ℝ} : X.vGe j F g ↔ ∃ F0 ∈ X.Int j, X.vsc g • F0 = F := by
  unfold Sys.vGe
  exact mem_scale

theorem vGe_zero (j : ℕ) (g : ℝ) : X.vGe j 0 g := by
  exact (vGe_iff X).2 ⟨0, (X.Int j).zero_mem, smul_zero _⟩

theorem vGe_add {j : ℕ} {F F' : X.Fm j} {g : ℝ} (h : X.vGe j F g) (h' : X.vGe j F' g) : X.vGe j (F + F') g := by
  obtain ⟨F0, h0, rfl⟩ := (vGe_iff X).1 h
  obtain ⟨F1, h1, rfl⟩ := (vGe_iff X).1 h'
  exact (vGe_iff X).2 ⟨F0 + F1, add_mem h0 h1, smul_add _ _ _⟩

theorem vGe_sum {j : ℕ} {ι : Type*} (s : Finset ι) (f : ι → X.Fm j) {g : ℝ} (h : ∀ i ∈ s, X.vGe j (f i) g) :
    X.vGe j (∑ i ∈ s, f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vGe_zero X j g
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact vGe_add X (h i (Finset.mem_insert.2 (Or.inl rfl))) (ih fun k hk => h k (Finset.mem_insert.2 (Or.inr hk)))

theorem vGe_mono (hfr : IsFractionRing X.G.O X.G.Kf) {j : ℕ} {F : X.Fm j} {g g' : ℝ} (h : g' ≤ g)
    (hF : X.vGe j F g) : X.vGe j F g' := by
  obtain ⟨F0, h0, rfl⟩ := (vGe_iff X).1 hF
  have hc : ⌈g' * (X.eO : ℝ)⌉ ≤ ⌈g * (X.eO : ℝ)⌉ := ceil_mono X h
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hc)
  refine (vGe_iff X).2 ⟨X.vp ^ k • F0, (X.Int j).smul_mem _ h0, ?_⟩
  have e : ⌈g * (X.eO : ℝ)⌉ = ⌈g' * (X.eO : ℝ)⌉ + k := by omega
  rw [← algebraMap_smul X.G.Kf (X.vp ^ k) F0, smul_smul]
  congr 1
  rw [vsc_def, vsc_def, e, zpow_add₀ (piK_ne X hfr), zpow_natCast, map_pow]

theorem vGe_zero_iff {j : ℕ} {F : X.Fm j} : X.vGe j F 0 ↔ F ∈ X.Int j := by
  rw [vGe_iff, vsc_def]
  simp

theorem vGe_smul (hfr : IsFractionRing X.G.O X.G.Kf) {j : ℕ} {a : X.G.Kf} {F : X.Fm j} {g h : ℝ}
    (ha : X.vGeK a g) (hF : X.vGe j F h) : X.vGe j (a • F) (g + h) := by
  obtain ⟨c, rfl⟩ := (vGeK_iff X).1 ha
  obtain ⟨F0, h0, rfl⟩ := (vGe_iff X).1 hF
  have hle : ⌈(g + h) * (X.eO : ℝ)⌉ ≤ ⌈g * (X.eO : ℝ)⌉ + ⌈h * (X.eO : ℝ)⌉ := by
    rw [Int.ceil_le]
    push_cast
    rw [add_mul]
    linarith [Int.le_ceil (g * (X.eO : ℝ)), Int.le_ceil (h * (X.eO : ℝ))]
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hle)
  refine (vGe_iff X).2 ⟨(X.vp ^ k * c) • F0, (X.Int j).smul_mem _ h0, ?_⟩
  have e : ⌈g * (X.eO : ℝ)⌉ + ⌈h * (X.eO : ℝ)⌉ = ⌈(g + h) * (X.eO : ℝ)⌉ + k := by omega
  have hz : piK X ^ ⌈g * (X.eO : ℝ)⌉ * piK X ^ ⌈h * (X.eO : ℝ)⌉ =
      piK X ^ ⌈(g + h) * (X.eO : ℝ)⌉ * algebraMap X.G.O X.G.Kf X.vp ^ k := by
    rw [← zpow_add₀ (piK_ne X hfr), e, zpow_add₀ (piK_ne X hfr), zpow_natCast]
  rw [← algebraMap_smul X.G.Kf (X.vp ^ k * c) F0, smul_smul, smul_smul]
  congr 1
  rw [vsc_def, vsc_def, vsc_def, map_mul, map_pow]
  linear_combination (-(algebraMap X.G.O X.G.Kf c)) * hz

end Val

section Num

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ}

theorem lamI_ge (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k1 + 1) :
    -w 1 s ≤ lamI lam0 s i := by
  unfold lamI
  rw [dif_pos ⟨h1, h2⟩]
  have hs := (h.w_low s).2
  have hd : lam0 s (Fin.last k1) ≤ lam0 s ⟨i - 1, by omega⟩ := h.dom s (by change i - 1 ≤ k1; omega)
  linarith

theorem w_le (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') {l l' : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ l')
    (h3 : l' ≤ m) : w l s ≤ w l' s := by
  induction l', h2 using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
    exact le_trans (ih (by omega)) (h.w_mono s n (by omega) (by omega))

theorem D_ge (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (l : ℕ) (hl : l ≤ r) :
    -(l : ℤ) * w 1 s ≤ ∑ i ∈ Icc 1 r, lamI lam0 s i - ∑ i ∈ Icc 1 (r - l), lamI lam0 s i := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hr := h.two_r
    have ih' := ih (by omega)
    have e : r - l = (r - (l + 1)) + 1 := by omega
    have hs := Finset.sum_Icc_succ_top (show 1 ≤ r - (l + 1) + 1 by omega) (fun i => lamI lam0 s i)
    rw [← e] at hs
    have hb := lamI_ge h s (r - l) (by omega) (by omega)
    push_cast
    linarith

theorem D_ge_al (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') :
    al TT lam0 s ≤ ∑ i ∈ Icc 1 r, lamI lam0 s i + (r : ℤ) * w 1 s := by
  have hr1 := h.r_pos
  have hr2 := h.two_r
  have hD := D_ge h s (r - 1) (by omega)
  have e1 : r - (r - 1) = 1 := by omega
  rw [e1, Finset.Icc_self, Finset.sum_singleton] at hD
  push_cast [Nat.cast_sub hr1] at hD
  have h2 := lamI_ge h s 2 (by omega) (by omega)
  have h1' := lamI_ge h s 1 (le_refl 1) (by omega)
  unfold al
  split_ifs <;> linarith

def muZ (t : ℕ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ℤ :=
  ∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s), w 1 s -
    ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), w j s - ((n' / 2 : ℕ) : ℤ) * t

def clExp (t r : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j l : ℕ) : ℤ :=
  (Nprime lam0 w j r - Nprime lam0 w j (r - l)) +
    ((n' / 2 : ℕ) : ℤ) * l * ((NN k1 t j : ℤ) - 2 * r + l) + (l : ℤ) * muZ t w j

theorem clExp_eq (j l : ℕ) (hl : l ≤ r) :
    clExp t r lam0 w j l =
      ∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s),
        (∑ i ∈ Icc 1 r, lamI lam0 s i - ∑ i ∈ Icc 1 (r - l), lamI lam0 s i + (l : ℤ) * w 1 s) +
      ((n' / 2 : ℕ) : ℤ) * l * ((NN k1 t j : ℤ) - 2 * r + l - t) := by
  unfold clExp muZ Nprime
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  push_cast [Nat.cast_sub hl]
  ring

theorem tail_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (j l : ℕ) :
    0 ≤ ((n' / 2 : ℕ) : ℤ) * l * ((NN k1 t (j + 1) : ℤ) - 2 * r + l - t) := by
  have hr := h.two_r
  have hr' : (2 * r : ℤ) ≤ k1 + 1 := by exact_mod_cast hr
  apply mul_nonneg (mul_nonneg (by positivity) (by positivity))
  unfold NN
  push_cast
  nlinarith [(by positivity : (0 : ℤ) ≤ (j : ℤ) * t), (by positivity : (0 : ℤ) ≤ (j : ℤ)),
    (by positivity : (0 : ℤ) ≤ (l : ℤ))]

theorem clExp_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (j l : ℕ) (hl : l ≤ r) :
    0 ≤ clExp t r lam0 w (j + 1) l := by
  rw [clExp_eq (j + 1) l hl]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro s _
    have := D_ge h s l hl
    linarith
  · exact tail_nonneg h j l

theorem clExp_ge_al (h : Std p n' k1 t m c r TT a b lam0 w) (j : ℕ) :
    ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), al TT lam0 s ≤ clExp t r lam0 w (j + 1) r := by
  rw [clExp_eq (j + 1) r le_rfl]
  have e1 : ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), al TT lam0 s =
      ∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s), al TT lam0 s := by
    refine Finset.sum_subset (fun s hs => ?_) (fun s hs hs' => ?_)
    · rw [mem_filter] at hs ⊢
      exact ⟨mem_univ _, hs.2⟩
    · rw [mem_filter] at hs hs'
      unfold al
      rw [if_neg fun hT => hs' ⟨hT, hs.2⟩]
  rw [e1]
  have e2 := tail_nonneg h j r
  have e3 : ∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s), al TT lam0 s ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s),
        (∑ i ∈ Icc 1 r, lamI lam0 s i - ∑ i ∈ Icc 1 (r - r), lamI lam0 s i + (r : ℤ) * w 1 s) := by
    refine Finset.sum_le_sum fun s _ => ?_
    have := D_ge_al h s
    simp only [Nat.sub_self]
    have e0 : ∑ i ∈ Icc 1 0, lamI lam0 s i = 0 := by simp
    rw [e0]
    linarith
  linarith

theorem mu_le (h : Std p n' k1 t m c r TT a b lam0 w) {j l i : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ j) (h3 : j ≤ m)
    (hi : i ≤ t) :
    muZ t w j ≤ (∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s), w l s -
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), w l s) + ((n' / 2 : ℕ) : ℤ) * ((t : ℤ) - 2 * i) := by
  unfold muZ
  have h1' : ∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s), w 1 s ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s), w l s :=
    Finset.sum_le_sum fun s _ => w_le h s (le_refl 1) h1 (by omega)
  have h2' : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), w l s ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), w j s :=
    Finset.sum_le_sum fun s _ => w_le h s h1 h2 h3
  have h4 : ((n' / 2 : ℕ) : ℤ) * i ≤ ((n' / 2 : ℕ) : ℤ) * t :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hi) (by positivity)
  linarith

end Num

section Cii

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem vGeK_FF (v : X.Pl) (m : ℕ → X.G.Kf) (hm : ∀ l ∈ Icc 1 X.mm, X.vEqK (m l) (X.vm v l)) (j : ℕ)
    (hj : j ≤ X.mm) (x : Fin j × Fin (X.t + 1)) :
    X.vGeK (X.FF v m j x) ((muZ X.t (X.w v) j : ℤ) : ℝ) := by
  have hfr := frac_of_place X v
  unfold Sys.FF Sys.qh
  have h1 : X.vGeK (m (x.1.val + 1)) (X.vm v (x.1.val + 1)) :=
    (hm _ (mem_Icc.2 ⟨by omega, by have := x.1.isLt; omega⟩)).1
  have h2 := vGeK_mul X hfr h1 (vGeK_ppow X hfr (((X.G.P.n' v / 2 : ℕ) : ℤ) * ((X.t : ℤ) - 2 * x.2.val)))
  refine vGeK_mono X hfr ?_ h2
  have h3 := mu_le (X.std v) (l := x.1.val + 1) (j := j) (i := x.2.val) (by omega) (by have := x.1.isLt; omega) hj
    (Nat.lt_succ_iff.1 x.2.isLt)
  have h4 : ((muZ X.t (X.w v) j : ℤ) : ℝ) ≤
      ((X.vm v (x.1.val + 1) + ((X.G.P.n' v / 2 : ℕ) : ℤ) * ((X.t : ℤ) - 2 * x.2.val) : ℤ) : ℝ) := by
    exact_mod_cast h3
  rw [Int.cast_add] at h4
  exact h4

theorem vGeK_hsymm (v : X.Pl) (m : ℕ → X.G.Kf) (hm : ∀ l ∈ Icc 1 X.mm, X.vEqK (m l) (X.vm v l)) (j : ℕ)
    (hj : j ≤ X.mm) (l : ℕ) :
    X.vGeK (MvPolynomial.eval (X.FF v m j) (MvPolynomial.hsymm (Fin j × Fin (X.t + 1)) X.G.Kf l))
      ((l : ℝ) * ((muZ X.t (X.w v) j : ℤ) : ℝ)) := by
  have hfr := frac_of_place X v
  rw [MvPolynomial.hsymm, map_sum]
  refine vGeK_sum X _ _ fun s _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  have h1 := vGeK_multiset_prod X hfr (fun x => X.FF v m j x) ((muZ X.t (X.w v) j : ℤ) : ℝ) s.1
    (fun x _ => vGeK_FF X v m hm j hj x)
  rw [s.2] at h1
  have e : Multiset.map (⇑(MvPolynomial.eval (X.FF v m j)) ∘ MvPolynomial.X) s.1 =
      Multiset.map (fun x => X.FF v m j x) s.1 := Multiset.map_congr rfl fun x _ => by simp
  rw [e]
  exact h1

theorem vGeK_cl (v : X.Pl) (m : ℕ → X.G.Kf) (hm : ∀ l ∈ Icc 1 X.mm, X.vEqK (m l) (X.vm v l)) (j : ℕ)
    (hj : j ≤ X.mm) (l : ℕ) :
    X.vGeK (X.cl v m j l) ((clExp X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j l : ℤ) : ℝ) := by
  have hfr := frac_of_place X v
  unfold Sys.cl
  have h := vGeK_mul X hfr (vGeK_mul X hfr
    (vGeK_ppow X hfr (Nprime (X.G.P.lam0 v) (X.w v) j X.G.P.r - Nprime (X.G.P.lam0 v) (X.w v) j (X.G.P.r - l)))
    (vGeK_ppow X hfr (((X.G.P.n' v / 2 : ℕ) : ℤ) * l * ((NN X.G.P.m X.t j : ℤ) - 2 * X.G.P.r + l))))
    (vGeK_hsymm X v m hm j hj l)
  refine vGeK_mono X hfr (le_of_eq ?_) h
  unfold clExp
  push_cast
  ring

theorem Cii (v : X.Pl) (m : ℕ → X.G.Kf) (hm : ∀ l ∈ Icc 1 X.mm, X.vEqK (m l) (X.vm v l)) (j : ℕ)
    (hj : j < X.mm) :
    (∀ l ≤ X.G.P.r, X.vGeK (X.cl v m (j + 1) l) 0) ∧
      X.vGeK (X.cl v m (j + 1) X.G.P.r) (X.alEven v) := by
  have hfr := frac_of_place X v
  constructor
  · intro l hl
    refine vGeK_mono X hfr ?_ (vGeK_cl X v m hm (j + 1) hj l)
    exact_mod_cast clExp_nonneg (X.std v) j l hl
  · refine vGeK_mono X hfr ?_ (vGeK_cl X v m hm (j + 1) hj X.G.P.r)
    exact_mod_cast clExp_ge_al (X.std v) j

theorem vEqK_mHat (v : X.Pl) (u m : ℕ → X.G.Kf) (hu : ∀ l ∈ Icc 1 X.mm, X.vEqK (u l) 0)
    (hm : ∀ l ∈ Icc 1 X.mm, X.vEqK (m l) (X.vm v l)) : ∀ l ∈ Icc 1 X.mm, X.vEqK (mHat u m l) (X.vm v l) := by
  intro l hl
  have hfr := frac_of_place X v
  obtain ⟨_, _, he, _⟩ := vEqK.rep X hfr (hm l hl)
  unfold mHat
  have h1 : X.vEqK (∏ l' ∈ Icc 1 (l - 1), u l') 0 :=
    vEqK_prod_units X hfr he _ _ fun l' hl' => hu l' (by rw [mem_Icc] at hl hl' ⊢; omega)
  have h2 := vEqK_mul X hfr (hm l hl) (vEqK_inv X hfr h1)
  simpa using h2

theorem theorem_of_alternate_form (D : Formalism.BasicNotions.D7) (h : KernelCommutationUpToUnits D X) : Conclusion4 D X := by
  intro v
  obtain ⟨u, m, hu, hm, H⟩ := h v
  exact ⟨u, mHat u m, hu, vEqK_mHat X v u m hu hm, fun j hj => (H j hj).2⟩

end Cii

section Ciii

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem vGeK_negOnePow (l : ℕ) : X.vGeK ((-1 : X.G.Kf) ^ l) 0 := by
  exact (vGeK_zero_iff X).2 ((mem_intK X).2 ⟨(-1) ^ l, by simp⟩)

theorem CiiiGen (v : X.Pl) (u mh : ℕ → X.G.Kf) (j : ℕ) (hu : ∀ l ∈ Icc 1 (j + 1), X.vEqK (u l) 0)
    (hc : ∀ l ≤ X.G.P.r, X.vGeK (X.cl v mh (j + 1) l) 0)
    (hcr : X.vGeK (X.cl v mh (j + 1) X.G.P.r) (X.alEven v)) (B : ℝ)
    (hB : ∀ i ∈ Icc 1 X.G.P.r, ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Tt v i (j + 1) (X.Kz j G)) B)
    (hA : ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Kz j G) (B - X.alEven v)) :
    ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Zop v u mh (j + 1) (X.Kz j G)) B := by
  intro G hG
  have hfr := frac_of_place X v
  obtain ⟨_, _, he, _⟩ := vEqK.rep X hfr (hu (j + 1) (mem_Icc.2 ⟨by omega, le_rfl⟩))
  have hU : ∀ i : ℕ, X.vGeK ((∏ l ∈ Icc 1 (j + 1), u l) ^ (-(i : ℤ))) 0 := by
    intro i
    have h1 : X.vEqK (∏ l ∈ Icc 1 (j + 1), u l) 0 := vEqK_prod_units X hfr he _ _ hu
    have h2 := (vEqK_zpow X hfr h1 (-(i : ℤ))).1
    simpa using h2
  unfold Sys.Zop
  refine vGe_sum X _ _ fun l hl => ?_
  have hl' : l ≤ X.G.P.r := Nat.lt_succ_iff.1 (mem_range.1 hl)
  unfold Sys.Ttu
  rcases eq_or_lt_of_le hl' with rfl | hlt
  · have h0 : X.Tt v (X.G.P.r - X.G.P.r) (j + 1) (X.Kz j G) = X.Kz j G := by
      unfold Sys.Tt
      rw [if_pos (Nat.sub_self _)]
    rw [h0]
    have h := vGe_smul X hfr (vGeK_mul X hfr (vGeK_negOnePow X X.G.P.r) hcr)
      (vGe_smul X hfr (hU (X.G.P.r - X.G.P.r)) (hA G hG))
    refine vGe_mono X hfr (le_of_eq ?_) h
    ring
  · have h := vGe_smul X hfr (vGeK_mul X hfr (vGeK_negOnePow X l) (hc l hl'))
      (vGe_smul X hfr (hU (X.G.P.r - l))
        (hB (X.G.P.r - l) (mem_Icc.2 ⟨by omega, Nat.sub_le _ _⟩) G hG))
    refine vGe_mono X hfr (le_of_eq ?_) h
    ring

theorem Ciii (D : Formalism.BasicNotions.D7) (h3 : PointsLemma D X) (h2b : MassRatio₂ D X) (v : X.Pl) (u m : ℕ → X.G.Kf)
    (hu : ∀ l ∈ Icc 1 X.mm, X.vEqK (u l) 0) (hm : ∀ l ∈ Icc 1 X.mm, X.vEqK (m l) (X.vm v l)) (j : ℕ)
    (hj : j < X.mm) : ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Zop v u m (j + 1) (X.Kz j G))
      (X.gv v (j + 1) + ∑ v' ∈ univ.erase v, X.g0v v' (j + 1) - X.dG j) := by
  obtain ⟨hc, hcr⟩ := Cii X v m hm j hj
  refine CiiiGen X v u m j (fun l hl => hu l (by rw [mem_Icc] at hl ⊢; omega)) hc hcr _ (h3 v j hj).2 ?_
  intro G hG
  refine vGe_mono X (frac_of_place X v) (le_of_eq ?_) (h2b v j hj G hG)
  ring

theorem eO_pos (v : X.Pl) : 0 < X.eO := by
  rcases Nat.eq_zero_or_pos X.eO with h0 | h0
  · exfalso
    have hS := X.G.P.setting v
    have hpu : IsUnit (p : X.G.O) := by
      have := X.eO_spec
      rw [h0, pow_zero] at this
      exact (associated_one_iff_isUnit).1 this
    let _ : Algebra (X.G.P.W v) X.G.O := (X.G.P.j v).toAlgebra
    have : Algebra.IsIntegral (X.G.P.W v) X.G.O := ⟨hS.finite.to_isIntegral⟩
    have hmax : (Ideal.span {(p : X.G.P.W v)}).IsMaximal := by
      have := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hS.p_unif
      rw [← this]
      exact IsLocalRing.maximalIdeal.isMaximal _
    have hker : RingHom.ker (algebraMap (X.G.P.W v) X.G.O) ≤ Ideal.span {(p : X.G.P.W v)} := by
      have := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hS.p_unif
      rw [← this]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := X.G.O)
      (Ideal.span {(p : X.G.P.W v)}) hker
    have hp : (p : X.G.P.W v) ∈ Q.comap (algebraMap (X.G.P.W v) X.G.O) := by
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at hp
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hpu)
  · exact h0

end Ciii

end Formalism.MainNotions.FormalGroupSystem.Pf

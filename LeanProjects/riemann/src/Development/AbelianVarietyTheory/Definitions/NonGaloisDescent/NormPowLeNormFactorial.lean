import Mathlib

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

class IsUnitBall (O K : Type) [CommRing O] [NormedField K] [Algebra O K] : Prop where
  inj : Function.Injective (algebraMap O K)
  mem_range_iff : ∀ x : K, x ∈ Set.range (algebraMap O K) ↔ ‖x‖ ≤ 1

instance (l : ℕ) [Fact l.Prime] : IsUnitBall ℤ_[l] ℚ_[l] where
  inj := Subtype.val_injective
  mem_range_iff x := ⟨fun ⟨y, h⟩ => h ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

section Weights

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_mul_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (hm : ∀ i j, w (i + j) ≤ w i * w j)
    {f g : K⟦X⟧} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : ∀ n, ‖coeff n f‖ * w n ≤ a)
    (hg : ∀ n, ‖coeff n g‖ * w n ≤ b) (n : ℕ) : ‖coeff n (f * g)‖ * w n ≤ a * b := by
  rw [coeff_mul]
  obtain ⟨p, hp, h⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty
    (Finset.HasAntidiagonal.nonempty_antidiagonal n) (fun p : ℕ × ℕ => coeff p.1 f * coeff p.2 g)
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  calc _ ≤ ‖coeff p.1 f * coeff p.2 g‖ * (w p.1 * w p.2) :=
        mul_le_mul h (hp' ▸ hm _ _) (hw _) (norm_nonneg _)
    _ = (‖coeff p.1 f‖ * w p.1) * (‖coeff p.2 g‖ * w p.2) := by rw [norm_mul]; ring
    _ ≤ a * b := mul_le_mul (hf _) (hg _) (mul_nonneg (norm_nonneg _) (hw _)) ha

theorem tendsto_coeff_mul {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (hm : ∀ i j, w (i + j) ≤ w i * w j)
    {f g : K⟦X⟧} (hf : Tendsto (fun n => ‖coeff n f‖ * w n) atTop (𝓝 0))
    (hg : Tendsto (fun n => ‖coeff n g‖ * w n) atTop (𝓝 0)) :
    Tendsto (fun n => ‖coeff n (f * g)‖ * w n) atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop] at *
  refine .squeeze tendsto_const_nhds
    (Finset.HasAntidiagonal.tendsto_sup'_antidiagonal_cofinite
      (tendsto_mul_cofinite_nhds_zero hf hg))
    (fun x ↦ mul_nonneg (by simp) (hw x)) fun n ↦ ?_
  rw [coeff_mul]
  obtain ⟨p, hp, h⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty
    (Finset.HasAntidiagonal.nonempty_antidiagonal n) (fun p : ℕ × ℕ => coeff p.1 f * coeff p.2 g)
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  refine le_trans ?_ (Finset.le_sup' _ hp)
  calc _ ≤ ‖coeff p.1 f * coeff p.2 g‖ * (w p.1 * w p.2) :=
        mul_le_mul h (hp' ▸ hm _ _) (hw _) (norm_nonneg _)
    _ = (‖coeff p.1 f‖ * w p.1) * (‖coeff p.2 g‖ * w p.2) := by rw [norm_mul]; ring

theorem norm_coeff_add_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (f g : K⟦X⟧) (n : ℕ) :
    ‖coeff n (f + g)‖ * w n ≤ max (‖coeff n f‖ * w n) (‖coeff n g‖ * w n) := by
  rw [← max_mul_of_nonneg _ _ (hw n), map_add]
  exact mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (hw n)

theorem norm_natCast_le_of_dvd {a b : ℕ} (h : a ∣ b) : ‖(b : K)‖ ≤ ‖(a : K)‖ := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K c)

variable (K) in

def wS (e n : ℕ) : ℝ := ‖((n / e).factorial : K)‖

theorem wS_nonneg (e n : ℕ) : 0 ≤ wS K e n := norm_nonneg _

theorem wS_le_one (e n : ℕ) : wS K e n ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _

theorem wS_add (e i j : ℕ) : wS K e (i + j) ≤ wS K e i * wS K e j := by
  unfold wS
  rw [← norm_mul, ← Nat.cast_mul]
  exact norm_natCast_le_of_dvd ((Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
    (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div _ _ _)))

theorem wS_anti (e : ℕ) {i j : ℕ} (h : i ≤ j) : wS K e j ≤ wS K e i :=
  norm_natCast_le_of_dvd (Nat.factorial_dvd_factorial (Nat.div_le_div_right h))

end Weights

section Rings

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]

variable {O K} in
omit [IsUltrametricDist K] in
theorem norm_algebraMap_le (c : O) : ‖algebraMap O K c‖ ≤ 1 :=
  (IsUnitBall.mem_range_iff _).1 ⟨c, rfl⟩

variable {O K} in
omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem algebraMap_eq_C (c : O) : algebraMap O K⟦X⟧ c = C (algebraMap O K c) :=
  PowerSeries.algebraMap_apply

def A : Subalgebra O K⟦X⟧ where
  carrier := {f | ∀ n, ‖coeff n f‖ ≤ 1}
  mul_mem' {f g} hf hg n := by
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
      zero_le_one zero_le_one (f := f) (g := g) (by simpa using hf) (by simpa using hg) n
  add_mem' {f g} hf hg n := by
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))
  algebraMap_mem' c n := by
    rw [algebraMap_eq_C, coeff_C]
    split_ifs
    · exact norm_algebraMap_le c
    · simp

variable {O K} in
theorem mem_A {f : K⟦X⟧} : f ∈ A O K ↔ ∀ n, ‖coeff n f‖ ≤ 1 := Iff.rfl

theorem range_map_eq_A : (PowerSeries.mapAlgHom (Algebra.ofId O K)).range = A O K := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩ n
    exact norm_algebraMap_le (K := K) (coeff n g)
  · intro hf
    choose c hc using fun n => (IsUnitBall.mem_range_iff (O := O) _).2 (hf n)
    exact ⟨PowerSeries.mk c, by
      ext n
      rw [← hc n]
      exact (coeff_map (algebraMap O K) n (PowerSeries.mk c)).trans (by rw [coeff_mk])⟩

def equivA : O⟦X⟧ ≃ₐ[O] A O K :=
  (AlgEquiv.ofInjective (PowerSeries.mapAlgHom (Algebra.ofId O K))
    (PowerSeries.map_injective (algebraMap O K) IsUnitBall.inj)).trans
    (Subalgebra.equivOfEq _ _ (range_map_eq_A O K))

@[simp] theorem coe_equivA (f : O⟦X⟧) :
    (equivA O K f : K⟦X⟧) = PowerSeries.map (algebraMap O K) f := rfl

def S (e : ℕ) : Subalgebra O K⟦X⟧ where
  carrier := {f | (∀ n, ‖coeff n f‖ * wS K e n ≤ 1) ∧
    Tendsto (fun n => ‖coeff n f‖ * wS K e n) atTop (𝓝 0)}
  mul_mem' hf hg := ⟨fun n => by
    simpa using norm_coeff_mul_le (wS_nonneg e) (wS_add e) zero_le_one zero_le_one hf.1 hg.1 n,
    tendsto_coeff_mul (wS_nonneg e) (wS_add e) hf.2 hg.2⟩
  add_mem' {f g} hf hg := ⟨fun n => (norm_coeff_add_le (wS_nonneg e) f g n).trans
      (max_le (hf.1 n) (hg.1 n)),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n))
      (norm_coeff_add_le (wS_nonneg e) f g) (by simpa using hf.2.max hg.2)⟩
  algebraMap_mem' c := by
    rw [algebraMap_eq_C]
    refine ⟨fun n => ?_, tendsto_const_nhds.congr' ?_⟩
    · rw [coeff_C]
      split_ifs
      · exact mul_le_one₀ (norm_algebraMap_le c) (wS_nonneg _ _) (wS_le_one _ _)
      · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      simp [coeff_C, hn.ne']

variable {O K} in
theorem mem_S {e : ℕ} {f : K⟦X⟧} : f ∈ S O K e ↔ (∀ n, ‖coeff n f‖ * wS K e n ≤ 1) ∧
    Tendsto (fun n => ‖coeff n f‖ * wS K e n) atTop (𝓝 0) := Iff.rfl

def rad (l : ℕ) (k : ℝ) : ℝ := (l : ℝ) ^ (-k)

theorem rad_nonneg (l : ℕ) (k : ℝ) : 0 ≤ rad l k := Real.rpow_nonneg (Nat.cast_nonneg l) _

def R (l : ℕ) (k : ℝ) : Subalgebra O K⟦X⟧ where
  carrier := {f | PowerSeries.IsRestricted (rad l k) f}
  mul_mem' := PowerSeries.isRestricted.mul _
  add_mem' := PowerSeries.isRestricted.add _
  algebraMap_mem' c := by
    rw [algebraMap_eq_C]
    exact PowerSeries.isRestricted_C _ _

variable {O K} in
theorem mem_R {l : ℕ} {k : ℝ} {f : K⟦X⟧} :
    f ∈ R O K l k ↔ Tendsto (fun n => ‖coeff n f‖ * rad l k ^ n) atTop (𝓝 0) :=
  PowerSeries.isRestricted_iff' _ _

variable {K} in

def normR (l : ℕ) (k : ℝ) (f : K⟦X⟧) : ℝ := ⨆ n, ‖coeff n f‖ * rad l k ^ n

variable {O K} in
theorem le_normR {l : ℕ} {k : ℝ} {f : K⟦X⟧} (hf : f ∈ R O K l k) (n : ℕ) :
    ‖coeff n f‖ * rad l k ^ n ≤ normR l k f :=
  le_ciSup (mem_R.1 hf).bddAbove_range n

variable {O K}

def away (B : Subalgebra O K⟦X⟧) (s : B) : Subalgebra O K⟦X⟧ where
  carrier := {f | ∃ n : ℕ, (s : K⟦X⟧) ^ n * f ∈ B}
  mul_mem' := by
    rintro f g ⟨n, hf⟩ ⟨m, hg⟩
    exact ⟨n + m, by convert B.mul_mem hf hg using 1; ring⟩
  add_mem' := by
    rintro f g ⟨n, hf⟩ ⟨m, hg⟩
    exact ⟨n + m, by
      convert B.add_mem (B.mul_mem (B.pow_mem s.2 m) hf) (B.mul_mem (B.pow_mem s.2 n) hg) using 1
      ring⟩
  algebraMap_mem' c := ⟨0, by simpa using B.algebraMap_mem c⟩

omit [IsUltrametricDist K] [IsUnitBall O K]

theorem mem_away {B : Subalgebra O K⟦X⟧} {s : B} {f : K⟦X⟧} :
    f ∈ away B s ↔ ∃ n : ℕ, (s : K⟦X⟧) ^ n * f ∈ B := Iff.rfl

theorem le_away (B : Subalgebra O K⟦X⟧) (s : B) : B ≤ away B s := fun _ hf => ⟨0, by simpa⟩

instance (B : Subalgebra O K⟦X⟧) (s : B) : Algebra B (away B s) :=
  (Subalgebra.inclusion (le_away B s)).toAlgebra

@[simp] theorem coe_algebraMap_away {B : Subalgebra O K⟦X⟧} {s : B} (f : B) :
    (algebraMap B (away B s) f : K⟦X⟧) = f := rfl

theorem isLocalization_away (B : Subalgebra O K⟦X⟧) (s : B) (hs : IsUnit (s : K⟦X⟧)) :
    IsLocalization.Away s (away B s) := by
  obtain ⟨t, ht⟩ := hs.exists_right_inv
  refine IsLocalization.Away.mk s ?_ ?_ ?_
  · exact IsUnit.of_mul_eq_one ⟨t, 1, by simpa [ht] using B.one_mem⟩ (Subtype.ext ht)
  · rintro ⟨f, n, hf⟩
    exact ⟨n, ⟨_, hf⟩, Subtype.ext (by simp [mul_comm])⟩
  · intro a b h
    have h' : (a : K⟦X⟧) = b := congrArg (fun x : away B s => (x : K⟦X⟧)) h
    exact ⟨0, by rw [Subtype.ext h']⟩

class HasU (B : Subalgebra O K⟦X⟧) : Prop where
  X_mem : (X : K⟦X⟧) ∈ B

class HasK (B : Subalgebra O K⟦X⟧) : Prop where
  C_mem : ∀ c : K, C c ∈ B

instance (B : Subalgebra O K⟦X⟧) [HasK B] : Algebra K B :=
  ((C : K →+* K⟦X⟧).codRestrict B HasK.C_mem).toAlgebra

@[simp] theorem coe_algebraMap_K {B : Subalgebra O K⟦X⟧} [HasK B] (c : K) :
    (algebraMap K B c : K⟦X⟧) = C c := rfl

instance (B : Subalgebra O K⟦X⟧) [HasK B] : IsScalarTower K B K⟦X⟧ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance (B : Subalgebra O K⟦X⟧) [HasK B] : IsScalarTower O K B :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (algebraMap_eq_C c)

instance (B : Subalgebra O K⟦X⟧) (s : B) [HasU B] : HasU (away B s) := ⟨le_away B s HasU.X_mem⟩

instance (B : Subalgebra O K⟦X⟧) (s : B) [HasK B] : HasK (away B s) :=
  ⟨fun c => le_away B s (HasK.C_mem c)⟩

variable (K) in

def E (l e : ℕ) : K⟦X⟧ := X ^ e + (l : K⟦X⟧)

theorem E_mem (l e : ℕ) (B : Subalgebra O K⟦X⟧) [HasU B] : E K l e ∈ B :=
  B.add_mem (B.pow_mem HasU.X_mem e) (natCast_mem B l)

def uIn (B : Subalgebra O K⟦X⟧) [HasU B] : B := ⟨X, HasU.X_mem⟩

def EIn (l e : ℕ) (B : Subalgebra O K⟦X⟧) [HasU B] : B := ⟨E K l e, E_mem l e B⟩

@[simp] theorem coe_uIn (B : Subalgebra O K⟦X⟧) [HasU B] : (uIn B : K⟦X⟧) = X := rfl

@[simp] theorem coe_EIn (l e : ℕ) (B : Subalgebra O K⟦X⟧) [HasU B] :
    (EIn l e B : K⟦X⟧) = E K l e := rfl

abbrev invL (l : ℕ) (B : Subalgebra O K⟦X⟧) : Subalgebra O K⟦X⟧ := away B (l : B)

abbrev invE (l e : ℕ) (B : Subalgebra O K⟦X⟧) [HasU B] : Subalgebra O K⟦X⟧ := away B (EIn l e B)

theorem away_mono {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {s : B} {s' : B'}
    (hs : (s : K⟦X⟧) = s') : away B s ≤ away B' s' := fun _ ⟨n, hn⟩ => ⟨n, hs ▸ h hn⟩

variable (K) in

def frob (l : ℕ) [Fact l.Prime] : K⟦X⟧ →ₐ[K] K⟦X⟧ :=
  PowerSeries.expand l (Fact.out : l.Prime).ne_zero

variable (K) in

def N : Derivation K K⟦X⟧ K⟦X⟧ := (X : K⟦X⟧) • PowerSeries.derivative K

theorem N_apply (f : K⟦X⟧) : N K f = X * PowerSeries.derivative K f := rfl

theorem coeff_N (f : K⟦X⟧) (n : ℕ) : coeff n (N K f) = n * coeff n f := by
  cases n with
  | zero => simp [N_apply]
  | succ n => rw [N_apply, coeff_succ_X_mul, coeff_derivative]; push_cast; ring

@[simp] theorem frob_X (l : ℕ) [Fact l.Prime] : frob K l X = X ^ l := expand_X _ _

@[simp] theorem frob_C (l : ℕ) [Fact l.Prime] (c : K) : frob K l (C c) = C c := expand_C _ _ c

theorem coeff_frob (l : ℕ) [Fact l.Prime] (f : K⟦X⟧) (n : ℕ) :
    coeff n (frob K l f) = if l ∣ n then coeff (n / l) f else 0 := coeff_expand _ _ f

@[simp] theorem constantCoeff_frob (l : ℕ) [Fact l.Prime] (f : K⟦X⟧) :
    constantCoeff (frob K l f) = constantCoeff f := constantCoeff_expand _ _ f

theorem frob_injective (l : ℕ) [Fact l.Prime] : Function.Injective (frob K l) := fun f g h => by
  ext n
  have := congrArg (coeff (l * n)) h
  simpa [frob] using this

theorem N_frob (l : ℕ) [Fact l.Prime] (f : K⟦X⟧) :
    N K (frob K l f) = (l : K⟦X⟧) * frob K l (N K f) := by
  ext n
  rw [← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul, coeff_N, coeff_frob, coeff_frob]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_N, Nat.mul_div_cancel_left _ (Fact.out : l.Prime).pos]
    push_cast; ring
  · simp

theorem N_E (l e : ℕ) : N K (E K l e) = (e : K⟦X⟧) * X ^ e := by
  ext n
  rw [coeff_N, E, ← map_natCast (C : K →+* K⟦X⟧) l, ← map_natCast (C : K →+* K⟦X⟧) e,
    coeff_C_mul, map_add, coeff_X_pow, coeff_C]
  by_cases h0 : n = 0
  · subst h0
    split_ifs with h1
    · subst h1; simp
    all_goals simp_all
  · split_ifs <;> simp_all

theorem constantCoeff_E (l e : ℕ) [NeZero e] : constantCoeff (E K l e) = l := by
  simp [E, NeZero.ne e]

end Rings

section Inst

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]

instance : HasU (A O K) := ⟨fun n => by rw [coeff_X]; split_ifs <;> simp⟩

variable {O K} in
theorem monomial_mem_S {e n : ℕ} {c : K} (h : ‖c‖ * wS K e n ≤ 1) : monomial n c ∈ S O K e := by
  refine ⟨fun m => ?_, tendsto_const_nhds.congr' ?_⟩
  · rw [coeff_monomial]
    split_ifs with hm
    · exact hm ▸ h
    · simp
  · filter_upwards [eventually_gt_atTop n] with m hm
    simp [coeff_monomial, hm.ne']

instance (e : ℕ) : HasU (S O K e) :=
  ⟨monomial_mem_S (n := 1) (c := 1) (by simpa using wS_le_one e 1)⟩

instance (l : ℕ) (k : ℝ) : HasU (R O K l k) := ⟨PowerSeries.isRestricted_monomial _ 1 1⟩

instance (l : ℕ) (k : ℝ) : HasK (R O K l k) := ⟨fun c => PowerSeries.isRestricted_C _ c⟩

variable {O K}

theorem frob_mem_A (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : f ∈ A O K) : frob K l f ∈ A O K := by
  intro n
  rw [coeff_frob]
  split_ifs
  · exact hf _
  · simp

theorem frob_bound (l : ℕ) [Fact l.Prime] {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (ha : Antitone w)
    (f : K⟦X⟧) (n : ℕ) : ‖coeff n (frob K l f)‖ * w n ≤ ‖coeff (n / l) f‖ * w (n / l) := by
  rw [coeff_frob]
  split_ifs
  · exact mul_le_mul_of_nonneg_left (ha (Nat.div_le_self _ _)) (norm_nonneg _)
  · simpa using mul_nonneg (norm_nonneg _) (hw _)

theorem frob_mem_S (l : ℕ) [Fact l.Prime] {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) :
    frob K l f ∈ S O K e :=
  ⟨fun n => (frob_bound l (wS_nonneg e) (fun _ _ => wS_anti e) f n).trans (hf.1 _),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n))
      (frob_bound l (wS_nonneg e) (fun _ _ => wS_anti e) f)
      (hf.2.comp (Nat.tendsto_div_const_atTop (Fact.out : l.Prime).ne_zero))⟩

theorem rad_le_one (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 ≤ k) : rad l k ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Fact.out : l.Prime).one_le) (by linarith)

theorem rad_lt_one (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 < k) : rad l k < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (Fact.out : l.Prime).one_lt) (by linarith)

theorem rad_pos (l : ℕ) [Fact l.Prime] (k : ℝ) : 0 < rad l k :=
  Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _

theorem frob_mem_R (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 ≤ k) {f : K⟦X⟧} (hf : f ∈ R O K l k) :
    frob K l f ∈ R O K l k :=
  mem_R.2 <| squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k) n))
    (frob_bound l (fun n => pow_nonneg (rad_nonneg l k) n)
      (fun _ _ h => pow_le_pow_of_le_one (rad_nonneg l k) (rad_le_one l hk) h) f)
    ((mem_R.1 hf).comp (Nat.tendsto_div_const_atTop (Fact.out : l.Prime).ne_zero))

theorem R_mono (l : ℕ) [Fact l.Prime] {k k' : ℝ} (h : k ≤ k') : R O K l k ≤ R O K l k' := fun f hf =>
  mem_R.2 <| squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k') n))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (rad_nonneg l k')
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : l.Prime).one_le)
        (by linarith)) n) (norm_nonneg _)) (mem_R.1 hf)

theorem A_le_R (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 < k) : A O K ≤ R O K l k := fun f hf =>
  mem_R.2 <| squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k) n))
    (fun n => mul_le_of_le_one_left (pow_nonneg (rad_nonneg l k) n) (hf n))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (rad_nonneg l k) (rad_lt_one l hk))

theorem norm_coeff_derivative_le (f : K⟦X⟧) (n : ℕ) :
    ‖coeff n (PowerSeries.derivative K f)‖ ≤ ‖coeff (n + 1) f‖ := by
  rw [coeff_derivative, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (n + 1))

theorem derivative_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : PowerSeries.derivative K f ∈ A O K :=
  fun n => (norm_coeff_derivative_le f n).trans (hf _)

theorem derivative_mem_R (l : ℕ) [Fact l.Prime] {k : ℝ} {f : K⟦X⟧} (hf : f ∈ R O K l k) :
    PowerSeries.derivative K f ∈ R O K l k := by
  have h := ((mem_R.1 hf).comp (tendsto_add_atTop_nat 1)).mul_const (rad l k)⁻¹
  rw [zero_mul] at h
  refine mem_R.2 <| squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k) n)) (fun n => ?_) h
  have := rad_pos l k
  calc _ ≤ ‖coeff (n + 1) f‖ * rad l k ^ n := by gcongr; exact norm_coeff_derivative_le f n
    _ = _ := by simp only [Function.comp]; field_simp; ring

theorem derivative_mem_S {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) :
    PowerSeries.derivative K f ∈ S O K e := by
  have key : ∀ n, ‖coeff n (PowerSeries.derivative K f)‖ * wS K e n ≤
      ‖coeff (n + 1) f‖ * wS K e (n + 1) := fun n => by
    rw [coeff_derivative, norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold wS
    rw [← norm_mul, ← Nat.cast_succ, ← Nat.cast_mul]
    refine norm_natCast_le_of_dvd ?_
    rw [Nat.succ_div]
    split_ifs with h
    · rw [Nat.factorial_succ]
      refine Nat.mul_dvd_mul_right ?_ _
      have := Nat.succ_div (a := n) (b := e)
      rw [if_pos h] at this
      rw [← this]
      exact Nat.div_dvd_of_dvd h
    · exact Dvd.intro_left _ rfl
  exact ⟨fun n => (key n).trans (hf.1 _),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) key
      (hf.2.comp (tendsto_add_atTop_nat 1))⟩

omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem derivative_mem_away {B : Subalgebra O K⟦X⟧} (s : B)
    (hB : ∀ f ∈ B, PowerSeries.derivative K f ∈ B) {f : K⟦X⟧} (hf : f ∈ away B s) :
    PowerSeries.derivative K f ∈ away B s := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n + 1, ?_⟩
  have h1 := B.mul_mem s.2 (hB _ hn)
  have h2 := B.mul_mem (B.mul_mem (natCast_mem B n) (hB _ s.2)) hn
  convert B.sub_mem h1 h2 using 1
  rw [Derivation.leibniz, derivative_pow]
  cases n with
  | zero => simp
  | succ n => simp only [smul_eq_mul, Nat.add_sub_cancel]; ring

omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem N_mem {B : Subalgebra O K⟦X⟧} [HasU B] {f : K⟦X⟧} (hf : PowerSeries.derivative K f ∈ B) :
    N K f ∈ B := B.mul_mem HasU.X_mem hf

omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem frob_mem_invL (l : ℕ) [Fact l.Prime] {B : Subalgebra O K⟦X⟧}
    (hB : ∀ f ∈ B, frob K l f ∈ B) {f : K⟦X⟧} (hf : f ∈ invL l B) : frob K l f ∈ invL l B := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by simpa using hB _ hn⟩

end Inst

section Padic

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

include l

omit [IsUltrametricDist K] in
theorem norm_natCast_eq (n : ℕ) : ‖(n : K)‖ = ‖(n : ℚ_[l])‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']

omit [IsUltrametricDist K] in

theorem norm_l : ‖(l : K)‖ = (l : ℝ)⁻¹ := by rw [norm_natCast_eq l, Padic.norm_p]

omit [IsUltrametricDist K] in
theorem natCast_ne_zero' {n : ℕ} (hn : n ≠ 0) : (n : K) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_natCast_eq l, norm_ne_zero_iff]
  exact_mod_cast hn

omit [IsUltrametricDist K] in
theorem l_ne_zero : (l : K) ≠ 0 := natCast_ne_zero' l (Fact.out : l.Prime).ne_zero

omit [IsUltrametricDist K] in
theorem norm_l_lt_one : ‖(l : K)‖ < 1 := by rw [norm_natCast_eq l]; exact Padic.norm_p_lt_one

omit [IsUltrametricDist K] in

theorem norm_pow_le_norm_factorial (m : ℕ) : ‖(l : K)‖ ^ m ≤ ‖(m.factorial : K)‖ := by
  rw [norm_l, norm_natCast_eq l, Padic.norm_eq_zpow_neg_valuation (by
    exact_mod_cast m.factorial_ne_zero), Padic.valuation_natCast, inv_pow, zpow_neg, zpow_natCast]
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (padicValNat_factorial_le l m))

theorem norm_factorial_le (m : ℕ) : ‖(m.factorial : K)‖ ≤ ‖(l : K)‖ ^ (m / l) := by
  rw [← norm_pow, ← Nat.cast_pow]
  refine norm_natCast_le_of_dvd (Dvd.dvd.trans ?_
    (Nat.factorial_dvd_factorial (Nat.mul_div_le m l)))
  rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero _), padicValNat_factorial_mul]
  omega

theorem tendsto_wS (e : ℕ) [NeZero e] : Tendsto (wS K e) atTop (𝓝 0) :=
  squeeze_zero (wS_nonneg e) (fun n => norm_factorial_le l (n / e))
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)).comp
      ((Nat.tendsto_div_const_atTop (Fact.out : l.Prime).ne_zero).comp
        (Nat.tendsto_div_const_atTop (NeZero.ne e))))

theorem A_le_S (e : ℕ) [NeZero e] : A O K ≤ S O K e := fun _ hf =>
  ⟨fun n => mul_le_one₀ (hf n) (wS_nonneg _ _) (wS_le_one _ _),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n))
      (fun n => mul_le_of_le_one_left (wS_nonneg e n) (hf n)) (tendsto_wS l e)⟩

omit [IsUltrametricDist K] in
theorem rad_pow (e : ℕ) [NeZero e] : rad l (1 / e) ^ e = ‖(l : K)‖ := by
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne e
  rw [norm_l, rad, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg l), neg_mul,
    one_div_mul_cancel he, Real.rpow_neg_one]

theorem S_le_R (e : ℕ) [NeZero e] : S O K e ≤ R O K l (1 / e) := fun f hf => by
  refine mem_R.2 <| squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l _) n)) (fun n => ?_) hf.2
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans ?_ (norm_pow_le_norm_factorial l (n / e))
  rw [← rad_pow l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le n e)

omit [IsUltrametricDist K] in
theorem exists_pow_mul_mem (c : K) : ∃ (n : ℕ) (b : O), (l : K) ^ n * c = algebraMap O K b := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
    (norm_l_lt_one (K := K) l)).mul_const ‖c‖
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
  obtain ⟨b, hb⟩ := (IsUnitBall.mem_range_iff (O := O) ((l : K) ^ n * c)).2
    (by rw [norm_mul, norm_pow]; exact hn.le)
  exact ⟨n, b, hb.symm⟩

instance (B : Subalgebra O K⟦X⟧) : HasK (invL l B) := ⟨fun c => by
  obtain ⟨n, b, h⟩ := exists_pow_mul_mem (O := O) l c
  refine ⟨n, ?_⟩
  convert B.algebraMap_mem b using 1
  rw [algebraMap_eq_C, ← h]
  simp⟩

omit [IsUltrametricDist K] in
theorem isUnit_l : IsUnit (l : K⟦X⟧) := by
  rw [← map_natCast (C : K →+* K⟦X⟧)]
  exact (l_ne_zero l).isUnit.map _

omit [IsUltrametricDist K] in
theorem isUnit_E (e : ℕ) [NeZero e] : IsUnit (E K l e) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_E]
  exact (l_ne_zero l).isUnit

instance (B : Subalgebra O K⟦X⟧) : IsLocalization.Away (l : B) (invL l B) :=
  isLocalization_away B _ (by simpa using isUnit_l l)

instance (e : ℕ) [NeZero e] (B : Subalgebra O K⟦X⟧) [HasU B] :
    IsLocalization.Away (EIn l e B) (invE l e B) :=
  isLocalization_away B _ (isUnit_E l e)

omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem invL_le {B B' : Subalgebra O K⟦X⟧} [HasK B'] (h : B ≤ B') : invL l B ≤ B' := by
  rintro f ⟨n, hn⟩
  have := B'.mul_mem (HasK.C_mem (((l : K) ^ n)⁻¹)) (h hn)
  convert this using 1
  have h2 : (((l : B) : K⟦X⟧)) = C (l : K) := by simp
  rw [h2, ← map_pow, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (l_ne_zero l)),
    map_one, one_mul]

variable (K) in

def Ediv (e i : ℕ) : K⟦X⟧ := C ((i.factorial : K)⁻¹) * E K l e ^ i

theorem Ediv_mem_S (e : ℕ) [NeZero e] (i : ℕ) : Ediv K l e i ∈ S O K e := by
  rw [Ediv, E, add_pow, Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun k hk => ?_
  have hk' : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hf (m : ℕ) : (m.factorial : K) ≠ 0 := natCast_ne_zero' l m.factorial_ne_zero
  have : C ((i.factorial : K)⁻¹) * ((X ^ e) ^ k * (l : K⟦X⟧) ^ (i - k) * (i.choose k : K⟦X⟧)) =
      monomial (e * k) ((k.factorial : K)⁻¹ * ((l : K) ^ (i - k) / ((i - k).factorial : K))) := by
    have h := congrArg (Nat.cast : ℕ → K) (Nat.choose_mul_factorial_mul_factorial hk')
    push_cast at h
    have h3 : (k.factorial : K)⁻¹ * ((l : K) ^ (i - k) / ((i - k).factorial : K)) =
        (i.factorial : K)⁻¹ * (l : K) ^ (i - k) * (i.choose k : K) := by
      have := hf k; have := hf (i - k); have := hf i
      field_simp
      linear_combination (-(l : K) ^ (i - k)) * h
    rw [h3, ← pow_mul, monomial_eq_C_mul_X_pow]
    simp only [map_mul, map_pow, map_natCast]
    ring
  rw [this]
  refine monomial_mem_S ?_
  have h1 : ‖(l : K) ^ (i - k) / ((i - k).factorial : K)‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ (norm_pow_le_norm_factorial l _) (norm_nonneg _)
  rw [wS, Nat.mul_div_cancel_left _ (NeZero.pos e), norm_mul, norm_inv, mul_right_comm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 (hf k)), one_mul]
  exact h1

variable (O K) in

def FilPre (e j : ℕ) : Ideal (S O K e) :=
  Ideal.span {x | ∃ i, j ≤ i ∧ (x : K⟦X⟧) = Ediv K l e i}

variable (O K) in

def Fil (e j : ℕ) : Ideal (S O K e) :=
  ⨅ n : ℕ, (FilPre O K l e j ⊔ Ideal.span {(l : S O K e) ^ n})

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem mem_Fil {e j : ℕ} {f : S O K e} : f ∈ Fil O K l e j ↔
    ∀ n : ℕ, ∃ g ∈ FilPre O K l e j, ∃ h : S O K e, f = g + (l : S O K e) ^ n * h := by
  simp only [Fil, Ideal.mem_iInf, Submodule.mem_sup, Ideal.mem_span_singleton']
  refine forall_congr' fun n => ⟨?_, ?_⟩
  · rintro ⟨g, hg, _, ⟨h, rfl⟩, rfl⟩
    exact ⟨g, hg, h, by ring⟩
  · rintro ⟨g, hg, h, rfl⟩
    exact ⟨g, hg, _, ⟨h, rfl⟩, by ring⟩

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem FilPre_le_Fil (e j : ℕ) : FilPre O K l e j ≤ Fil O K l e j :=
  le_iInf fun _ => le_sup_left

theorem Ediv_mem_Fil (e : ℕ) [NeZero e] {j i : ℕ} (h : j ≤ i) :
    (⟨Ediv K l e i, Ediv_mem_S l e i⟩ : S O K e) ∈ Fil O K l e j :=
  FilPre_le_Fil l e j (Ideal.subset_span ⟨i, h, rfl⟩)

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem Fil_anti (e : ℕ) {i j : ℕ} (h : i ≤ j) : Fil O K l e j ≤ Fil O K l e i :=
  iInf_mono fun _ => sup_le_sup_right
    (Ideal.span_mono (by rintro x ⟨k, hk, hx⟩; exact ⟨k, h.trans hk, hx⟩)) _

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem Fil_zero (e : ℕ) : Fil O K l e 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (FilPre_le_Fil l e 0 (Ideal.subset_span ⟨0, le_rfl, by simp [Ediv]⟩))

end Padic

end GlobalTheory.BK

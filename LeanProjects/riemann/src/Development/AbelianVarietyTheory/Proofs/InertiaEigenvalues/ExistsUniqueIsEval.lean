import Mathlib

namespace GlobalTheory.DiscEval

open PowerSeries Finset

variable (p : ℕ) {A K C B C' B' : Type*} [CommRing A] [CommRing K] [CommRing C] [CommRing B] [CommRing C']
  [CommRing B']

def Tends (i : C →+* B) (s : ℕ → B) (y : B) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ z : C, s n - y = i ((p : C) ^ r * z)

def OnDisc (a : A →+* K) (L : PowerSeries K) : Prop :=
  ∀ M : ℕ, 0 < M → ∃ D : ℕ, ∀ k : ℕ, ∃ b : A, (p : K) ^ (D + k / M) * coeff k L = a b

noncomputable def psum (κ : K →+* B) (L : PowerSeries K) (x : B) (n : ℕ) : B :=
  ∑ k ∈ range n, κ (coeff k L) * x ^ k

def IsEval (i : C →+* B) (κ : K →+* B) (L : PowerSeries K) (x y : B) : Prop := Tends p i (psum κ L x) y

variable {p} {i : C →+* B} {i' : C' →+* B'} {κ : K →+* B} {a : A →+* K} {o : A →+* C}

theorem eq_zero_of_dvd [h : IsHausdorff (Ideal.span {(p : C)}) C] {z : C} (hz : ∀ r : ℕ, (p : C) ^ r ∣ z) :
    z = 0 :=
  h.haus' z fun r => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hz r

theorem Tends.unique [IsHausdorff (Ideal.span {(p : C)}) C] (hi : Function.Injective i) {s : ℕ → B} {y y' : B}
    (h : Tends p i s y) (h' : Tends p i s y') : y = y' := by
  have key : ∀ r : ℕ, ∃ z : C, y - y' = i ((p : C) ^ r * z) := fun r => by
    obtain ⟨N, hN⟩ := h r
    obtain ⟨N', hN'⟩ := h' r
    obtain ⟨z, hz⟩ := hN (max N N') (le_max_left _ _)
    obtain ⟨z', hz'⟩ := hN' (max N N') (le_max_right _ _)
    exact ⟨z' - z, by rw [mul_sub, map_sub, ← hz, ← hz']; ring⟩
  obtain ⟨z, hz⟩ := key 0
  rw [pow_zero, one_mul] at hz
  have : z = 0 := eq_zero_of_dvd (p := p) fun r => (key r).imp fun w hw => hi (hz.symm.trans hw)
  rwa [this, map_zero, sub_eq_zero] at hz

theorem Tends.map (ψ : B →+* B') (hψ : ∀ z, ∃ z', ψ (i z) = i' z') {s : ℕ → B} {y : B}
    (h : Tends p i s y) : Tends p i' (fun n => ψ (s n)) (ψ y) := fun r =>
  (h r).imp fun N hN n hn => by
    obtain ⟨z, hz⟩ := hN n hn
    obtain ⟨z', hz'⟩ := hψ z
    exact ⟨z', by simp only [← map_sub, hz, map_mul, map_pow, map_natCast, hz']⟩

theorem Tends.const (y : B) : Tends p i (fun _ => y) y := fun _ => ⟨0, fun _ _ => ⟨0, by simp⟩⟩

theorem Tends.add {s t : ℕ → B} {y w : B} (h : Tends p i s y) (h' : Tends p i t w) :
    Tends p i (fun n => s n + t n) (y + w) := fun r => by
  obtain ⟨N, hN⟩ := h r
  obtain ⟨N', hN'⟩ := h' r
  refine ⟨max N N', fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN n (le_of_max_le_left hn)
  obtain ⟨z', hz'⟩ := hN' n (le_of_max_le_right hn)
  exact ⟨z + z', by rw [mul_add, map_add, ← hz, ← hz']; ring⟩

theorem Tends.mul_left (hp : IsUnit (p : B)) {c : B} (hc : ∃ (D : ℕ) (z : C), (p : B) ^ D * c = i z)
    {s : ℕ → B} {y : B} (h : Tends p i s y) : Tends p i (fun n => c * s n) (c * y) := fun r => by
  obtain ⟨D, w, hw⟩ := hc
  refine (h (D + r)).imp fun N hN n hn => ?_
  obtain ⟨z, hz⟩ := hN n hn
  refine ⟨w * z, ?_⟩
  simp only [← mul_sub, hz, map_mul, map_pow, map_natCast, ← hw]
  ring

theorem Tends.tendsto {F : Type*} [NormedField F] (ψ : B →+* F) (hψ : ∀ z, ‖ψ (i z)‖ ≤ 1) (hp : ‖(p : F)‖ < 1)
    {s : ℕ → B} {y : B} (h : Tends p i s y) : Filter.Tendsto (fun n => ψ (s n)) Filter.atTop (nhds (ψ y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε hp
  refine (h r).imp fun N hN n hn => ?_
  obtain ⟨z, hz⟩ := hN n hn
  rw [dist_eq_norm, ← map_sub, hz]
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hψ z)) hr

theorem exists_sum [h : IsPrecomplete (Ideal.span {(p : C)}) C] {N : ℕ} (hN : 0 < N) (t : ℕ → C)
    (ht : ∀ k, (p : C) ^ (k / N) ∣ t k) : ∃ S : C, ∀ n, (p : C) ^ (n / N) ∣ ∑ k ∈ range n, t k - S := by
  have h1 : ∀ m n, m ≤ n → (p : C) ^ (m / N) ∣ ∑ k ∈ range m, t k - ∑ k ∈ range n, t k := fun m n hmn => by
    rw [← neg_sub, dvd_neg, ← sum_Ico_eq_sub _ hmn]
    exact dvd_sum fun k hk => (pow_dvd_pow _ (Nat.div_le_div_right (mem_Ico.1 hk).1)).trans (ht k)
  obtain ⟨S, hS⟩ := h.prec' (fun n => ∑ k ∈ range (n * N), t k) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have := h1 _ _ (Nat.mul_le_mul_right N hmn)
    rwa [Nat.mul_div_cancel _ hN] at this
  refine ⟨S, fun n => ?_⟩
  have h2 := hS (n / N)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  have h3 := h1 _ _ (Nat.div_mul_le_self n N)
  rw [Nat.mul_div_cancel _ hN] at h3
  have := dvd_sub h2 h3
  rwa [show ∀ u v w : C, u - v - (u - w) = w - v from fun u v w => by ring] at this

theorem pow_div_dvd {x : C} {M : ℕ} (hx : (p : C) ∣ x ^ M) (k : ℕ) : (p : C) ^ (k / M) ∣ x ^ k := by
  refine (pow_dvd_pow_of_dvd hx _).trans ?_
  rw [← pow_mul]
  exact pow_dvd_pow _ (Nat.mul_div_le k M)

theorem two_mul_div_le (k M : ℕ) : k / (M * 2) + k / (M * 2) ≤ k / M := by
  rw [← Nat.div_div_eq_div_mul]
  omega

theorem exists_pos_pow {x : C} (hx : ∃ M : ℕ, (p : C) ∣ x ^ M) : ∃ M : ℕ, 0 < M ∧ (p : C) ∣ x ^ M :=
  hx.elim fun M hM => ⟨M + 1, M.succ_pos, hM.trans (pow_dvd_pow _ M.le_succ)⟩

theorem term_bound (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} {M D : ℕ}
    (hD : ∀ k : ℕ, ∃ b : A, (p : K) ^ (D + k / (M * 2)) * coeff k L = a b) {k n : ℕ} (hk : k ≤ n) {z : C}
    (hz : (p : C) ^ (n / M) ∣ z) :
    ∃ w : C, (p : B) ^ D * (κ (coeff k L) * i z) = i ((p : C) ^ (n / (M * 2)) * w) := by
  obtain ⟨b, hb⟩ := hD k
  obtain ⟨w, rfl⟩ := hz
  have h1 : k / (M * 2) + n / (M * 2) ≤ n / M :=
    (Nat.add_le_add_right (Nat.div_le_div_right hk) _).trans (two_mul_div_le n M)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
  have h2 := congrArg κ hb
  refine ⟨(p : C) ^ d * o b * w, ?_⟩
  simp only [map_mul, map_pow, map_natCast, h, hd, ← h2]
  ring

theorem exists_isEval_rate [IsPrecomplete (Ideal.span {(p : C)}) C] (hp : IsUnit (p : B))
    (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} (hL : OnDisc p a L) {x : C}
    (hx : ∃ M : ℕ, (p : C) ∣ x ^ M) : ∃ y : B, IsEval p i κ L (i x) y ∧ ∃ D N : ℕ, 0 < N ∧
      (∀ k, ∃ w : C, (p : B) ^ D * (κ (coeff k L) * i x ^ k) = i ((p : C) ^ (k / N) * w)) ∧
      ∀ n, ∃ w : C, (p : B) ^ D * (psum κ L (i x) n - y) = i ((p : C) ^ (n / N) * w) := by
  obtain ⟨M, hM, hx⟩ := exists_pos_pow hx
  have hN : 0 < M * 2 := by omega
  obtain ⟨D, hD⟩ := hL (M * 2) hN
  have ht := fun k => term_bound h hD (le_refl k) (pow_div_dvd hx k)
  simp only [map_pow i x] at ht
  choose w hw using id ht
  obtain ⟨S, hS⟩ := exists_sum hN (fun k => (p : C) ^ (k / (M * 2)) * w k) fun k => dvd_mul_right _ _
  obtain ⟨u, hu⟩ := (hp.pow D).exists_right_inv
  have hr : ∀ n, ∃ w : C, (p : B) ^ D * (psum κ L (i x) n - u * i S) = i ((p : C) ^ (n / (M * 2)) * w) :=
    fun n => (hS n).imp fun z hz => by
      rw [← hz, map_sub, map_sum, mul_sub, ← mul_assoc, hu, one_mul, psum, mul_sum]
      simp only [hw]
  refine ⟨u * i S, fun r => ⟨(D + r) * (M * 2), fun n hn => ?_⟩, D, M * 2, hN, ht, hr⟩
  obtain ⟨z, hz⟩ := hr n
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ((Nat.le_div_iff_mul_le hN).2 hn)
  refine ⟨(p : C) ^ d * z, (hp.pow D).mul_left_cancel ?_⟩
  simp only [hz, hd, map_mul, map_pow, map_natCast]
  ring

theorem existsUnique_isEval [IsAdicComplete (Ideal.span {(p : C)}) C] (hi : Function.Injective i)
    (hp : IsUnit (p : B)) (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} (hL : OnDisc p a L) {x : C}
    (hx : ∃ M : ℕ, (p : C) ∣ x ^ M) : ∃! y : B, IsEval p i κ L (i x) y :=
  (exists_isEval_rate hp h hL hx).elim fun y hy => ⟨y, hy.1, fun _ h' => Tends.unique hi h' hy.1⟩

theorem IsEval.map {K' : Type*} [CommRing K'] {κ' : K' →+* B'} (ψ : B →+* B') (τ : K →+* K')
    (hψ : ∀ z, ∃ z', ψ (i z) = i' z') (hκ : ∀ c, ψ (κ c) = κ' (τ c)) {L : PowerSeries K} {x y : B}
    (h : IsEval p i κ L x y) : IsEval p i' κ' (PowerSeries.map τ L) (ψ x) (ψ y) := by
  have := Tends.map ψ hψ h
  intro r
  simpa only [psum, map_sum, map_mul, map_pow, hκ, coeff_map] using this r

theorem IsEval.C_mul (hp : IsUnit (p : B)) {c : K} (hc : ∃ (D : ℕ) (z : C), (p : B) ^ D * κ c = i z)
    {L : PowerSeries K} {x y : B} (h : IsEval p i κ L x y) : IsEval p i κ (PowerSeries.C c * L) x (κ c * y) := by
  have := Tends.mul_left hp hc h
  intro r
  simpa only [psum, coeff_C_mul, map_mul, mul_sum, mul_assoc] using this r

theorem IsEval.add {L L' : PowerSeries K} {x y y' : B} (h : IsEval p i κ L x y) (h' : IsEval p i κ L' x y') :
    IsEval p i κ (L + L') x (y + y') := by
  have := Tends.add h h'
  intro r
  simpa only [psum, map_add, add_mul, sum_add_distrib] using this r

theorem pow_sub_dvd (u : PowerSeries A) {x y d : C} {n : ℕ} (hx : d ∣ x ^ n)
    (hy : d ∣ y - ∑ j ∈ range n, o (coeff j u) * x ^ j) (k : ℕ) :
    d ∣ y ^ k - ∑ j ∈ range n, o (coeff j (u ^ k)) * x ^ j := by
  have e : ∀ v : PowerSeries A, ∑ j ∈ range n, o (coeff j v) * x ^ j = Polynomial.eval₂RingHom o x (trunc n v) :=
    fun v => (eval₂_trunc_eq_sum_range x o n v).symm
  rw [e] at hy ⊢
  have h1 : Polynomial.X ^ n ∣ trunc n u ^ k - trunc n (u ^ k) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro j hj
    rw [Polynomial.coeff_sub, ← trunc_trunc_pow, coeff_trunc, if_pos hj, ← Polynomial.coe_pow,
      Polynomial.coeff_coe, sub_self]
  have h2 := map_dvd (Polynomial.eval₂RingHom o x) h1
  rw [map_pow, map_sub, map_pow, show Polynomial.eval₂RingHom o x Polynomial.X = x from
    Polynomial.eval₂_X o x] at h2
  have := dvd_add (hy.trans (sub_dvd_pow_sub_pow _ _ k)) (hx.trans h2)
  rwa [sub_add_sub_cancel] at this

theorem coeff_pow_of_lt {u : PowerSeries K} (hu : constantCoeff u = 0) {m k : ℕ} (h : k < m) :
    coeff k (u ^ m) = 0 := by
  obtain ⟨v, rfl⟩ := X_dvd_iff.2 hu
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

theorem IsEval.subst (hp : IsUnit (p : B)) (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} (hL : OnDisc p a L)
    {u : PowerSeries A} (hu : constantCoeff u = 0) {x y : C} {M : ℕ} (hM : 0 < M) (hx : (p : C) ∣ x ^ M)
    (hy : ∀ n, (p : C) ^ (n / M) ∣ y - ∑ j ∈ range n, o (coeff j u) * x ^ j) {w : B}
    (hw : IsEval p i κ L (i y) w) : IsEval p i κ (L.subst (PowerSeries.map a u)) (i x) w := by
  have hN : 0 < M * 2 := by omega
  obtain ⟨D, hD⟩ := hL (M * 2) hN
  have hu' : constantCoeff (PowerSeries.map a u) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu, map_zero]
  have hc : ∀ n j, j < n → coeff j (L.subst (PowerSeries.map a u)) =
      ∑ k ∈ range n, coeff k L * a (coeff j (u ^ k)) := fun n j hj => by
    rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hu'), finsum_eq_sum_of_support_subset (s := range n)]
    · simp only [smul_eq_mul, ← map_pow, coeff_map]
    · intro m hm
      rw [Function.mem_support] at hm
      by_contra hc
      simp only [coe_range, Set.mem_Iio, not_lt] at hc
      exact hm (by rw [coeff_pow_of_lt hu' (by omega), smul_zero])
  have hs : ∀ n, psum κ L (i y) n - psum κ (L.subst (PowerSeries.map a u)) (i x) n =
      ∑ k ∈ range n, κ (coeff k L) * i (y ^ k - ∑ j ∈ range n, o (coeff j (u ^ k)) * x ^ j) := fun n => by
    have e : psum κ (L.subst (PowerSeries.map a u)) (i x) n =
        ∑ j ∈ range n, ∑ k ∈ range n, κ (coeff k L * a (coeff j (u ^ k))) * i x ^ j :=
      sum_congr rfl fun j hj => by rw [hc n j (mem_range.1 hj), map_sum, sum_mul]
    rw [e, psum, sum_comm, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [map_sub, map_sum, map_mul, map_pow i, h, mul_sub, mul_sum, mul_assoc]
  intro r
  obtain ⟨N, hN'⟩ := hw r
  refine ⟨max N ((D + r) * (M * 2)), fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN' n (le_of_max_le_left hn)
  choose! v hv using fun k (hk : k ∈ range n) =>
    term_bound h hD (mem_range.1 hk).le (pow_sub_dvd u (pow_div_dvd hx n) (hy n) k)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ((Nat.le_div_iff_mul_le hN).2 (le_of_max_le_right hn))
  have h2 : psum κ L (i y) n - psum κ (L.subst (PowerSeries.map a u)) (i x) n =
      i ((p : C) ^ r * ((p : C) ^ d * ∑ k ∈ range n, v k)) := by
    refine (hp.pow D).mul_left_cancel ?_
    rw [hs, mul_sum, sum_congr rfl hv, ← map_sum, ← mul_sum]
    simp only [hd, map_mul, map_pow, map_natCast]
    ring
  exact ⟨z - (p : C) ^ d * ∑ k ∈ range n, v k, by rw [mul_sub, map_sub, ← hz, ← h2]; ring⟩

theorem onDisc_of_log {π : A} (hπ : π ∣ (p : A)) {q : ℕ} (hq : 1 < q) {L : PowerSeries K}
    (hL : ∀ k, ∃ b : A, a π ^ Nat.log q k * coeff k L = a b) : OnDisc p a L := fun M hM => by
  refine ⟨M, fun k => ?_⟩
  obtain ⟨b, hb⟩ := hL k
  obtain ⟨c, hc⟩ := hπ
  have h1 : Nat.log q k ≤ M + k / M := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    refine (Nat.log_lt_of_lt_pow hk.ne' ?_).le
    rw [pow_add]
    refine (Nat.lt_mul_div_succ k hM).trans_le (Nat.mul_le_mul (Nat.lt_pow_self hq).le (Nat.lt_pow_self hq))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
  refine ⟨c ^ Nat.log q k * (p : A) ^ d * b, ?_⟩
  have h2 : (p : K) = a π * a c := by rw [← map_mul, ← hc, map_natCast]
  simp only [hd, map_mul, map_pow, map_natCast, ← hb, pow_add]
  rw [show (p : K) ^ Nat.log q k = (a π * a c) ^ Nat.log q k by rw [h2]]
  ring

end GlobalTheory.DiscEval

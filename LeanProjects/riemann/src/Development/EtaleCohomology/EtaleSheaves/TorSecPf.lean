import Development.EtaleCohomology.EtaleSheaves.LCSplitPf

noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf

namespace LateralTheory.E.TorSecPf

section Loc
variable {S : Type} [CommRing S] (u v : S) {w : S}

lemma loc_surj (hw : u * v = w) (ρ : Localization.Away u →+* Localization.Away w)
    (hρ : ∀ a, ρ (algebraMap S _ a) = algebraMap S _ a) (z : Localization.Away w) :
    ∃ (n : ℕ) (y : Localization.Away u), algebraMap S _ v ^ n * z = ρ y := by
  subst hw
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (u * v) z
  refine ⟨n, algebraMap S _ a * IsLocalization.Away.invSelf u ^ n, ?_⟩
  have hu : algebraMap S (Localization.Away (u * v)) u * ρ (IsLocalization.Away.invSelf u) = 1 := by
    rw [← hρ, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  rw [map_mul, map_pow, hρ, ← h]
  simp only [map_mul, mul_pow]
  calc algebraMap S _ v ^ n * z = algebraMap S _ v ^ n * z * (algebraMap S (Localization.Away (u * v)) u * ρ (IsLocalization.Away.invSelf u)) ^ n := by
        rw [hu, one_pow, mul_one]
    _ = _ := by ring

lemma loc_ker (hw : u * v = w) (ρ : Localization.Away u →+* Localization.Away w)
    (hρ : ∀ a, ρ (algebraMap S _ a) = algebraMap S _ a) (y : Localization.Away u) (hy : ρ y = 0) :
    ∃ n : ℕ, algebraMap S _ v ^ n * y = 0 := by
  subst hw
  obtain ⟨m, a, h⟩ := IsLocalization.Away.surj u y
  have : algebraMap S (Localization.Away (u * v)) a = 0 := by
    rw [← hρ, ← h, map_mul, hy, zero_mul]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (u * v)) _ a).1 this
  refine ⟨n, ?_⟩
  have hunit : IsUnit (algebraMap S (Localization.Away u) u ^ (n + m)) :=
    (IsLocalization.Away.algebraMap_isUnit u).pow _
  apply hunit.mul_left_cancel
  rw [mul_zero]
  calc algebraMap S (Localization.Away u) u ^ (n + m) * (algebraMap S _ v ^ n * y)
      = algebraMap S _ ((u * v) ^ n * a) := by rw [map_mul (algebraMap _ _) ((u * v) ^ n) a, ← h, map_pow, map_mul]; ring
    _ = 0 := by simp only at hn; rw [hn, map_zero]
end Loc

section T
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] {f g : S} {ε : ZMod q → Localization.Away (f * g)}

lemma mem_tor (hε : CompleteOrthogonalIdempotents ε) (x : Amb f g q) :
    x ∈ Tor f g hε ↔ ∀ k, rL f g (x.1 k) = ∑ c, ε c * rR f g (x.2 (k + c)) := by
  show h1 f g x = h2 f g hε x ↔ _
  rw [funext_iff]; rfl

lemma rL_alg (a : S) : rL f g (algebraMap S _ a) = algebraMap S _ a :=
  IsLocalization.Away.awayToAwayRight_eq f g a
lemma rR_alg (a : S) : rR f g (algebraMap S _ a) = algebraMap S _ a :=
  IsLocalization.Away.awayToAwayLeft_eq g f a
end T

section LC
variable {q : ℕ} [NeZero q] {R : Type} [CommRing R] {δ : ZMod q → R}

lemma exists_not_mem (hδ : CompleteOrthogonalIdempotents δ) (p : PrimeSpectrum R) : ∃ k, δ k ∉ p.asIdeal := by
  by_contra h
  push_neg at h
  apply p.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hδ.complete]
  exact Ideal.sum_mem _ fun k _ => h k

lemma uniq (hδ : CompleteOrthogonalIdempotents δ) (p : PrimeSpectrum R) {j k : ZMod q}
    (hj : δ j ∉ p.asIdeal) (hk : δ k ∉ p.asIdeal) : j = k := by
  by_contra hjk
  have : δ j * δ k ∈ p.asIdeal := by rw [hδ.ortho hjk]; exact p.asIdeal.zero_mem
  rcases p.isPrime.mem_or_mem this with h | h
  · exact hj h
  · exact hk h

def lcOf (hδ : CompleteOrthogonalIdempotents δ) : LocallyConstant (PrimeSpectrum R) (ZMod q) where
  toFun p := Classical.choose (exists_not_mem hδ p)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    have : (fun p => Classical.choose (exists_not_mem hδ p)) ⁻¹' {y} =
        (PrimeSpectrum.basicOpen (δ y) : Set (PrimeSpectrum R)) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
      constructor
      · rintro rfl; exact Classical.choose_spec (exists_not_mem hδ p)
      · intro h; exact uniq hδ p (Classical.choose_spec (exists_not_mem hδ p)) h
    rw [this]; exact (PrimeSpectrum.basicOpen (δ y)).isOpen

lemma lcOf_spec (hδ : CompleteOrthogonalIdempotents δ) (p : PrimeSpectrum R) : δ (lcOf hδ p) ∉ p.asIdeal :=
  Classical.choose_spec (exists_not_mem hδ p)
end LC

section Tw
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

lemma eps_mul_sum (hε : CompleteOrthogonalIdempotents ε) (d : ZMod q) (z : ZMod q → A) :
    ε d * ∑ c, ε c * z c = ε d * z d := by
  rw [Finset.mul_sum, Finset.sum_eq_single d]
  · rw [← mul_assoc, (hε.idem d).eq]
  · intro c _ hcd; rw [← mul_assoc, hε.ortho (Ne.symm hcd), zero_mul]
  · simp

lemma twist_inj (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A)
    (h : ∀ k, ∑ c, ε c * z (k + c) = 0) (m : ZMod q) : z m = 0 := by
  have hd : ∀ d, ε d * z m = 0 := by
    intro d
    have := congrArg (ε d * ·) (h (m - d))
    simp only [mul_zero] at this
    rw [eps_mul_sum hε d, sub_add_cancel] at this
    exact this
  rw [← one_mul (z m), ← hε.complete, Finset.sum_mul]
  exact Finset.sum_eq_zero fun d _ => hd d

lemma twist_inv (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (j : ZMod q) :
    ∑ c, ε c * (∑ d, ε d * z (j + c - d)) = z j := by
  rw [Finset.sum_congr rfl fun c _ => by rw [eps_mul_sum hε c, add_sub_cancel_right], ← Finset.sum_mul,
    hε.complete, one_mul]
end Tw

section Main
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] {f g : S} {ε : ZMod q → Localization.Away (f * g)}
  (hε : CompleteOrthogonalIdempotents ε)
include hε

lemma kill (s : Tor f g hε →+* S) (hs : ∀ a, s (torMap f g hε a) = a) (t : Tor f g hε) (a : S)
    (h1 : ∀ k, ∃ n : ℕ, algebraMap S (Localization.Away f) a ^ n * (t : Amb f g q).1 k = 0)
    (h2 : ∀ k, ∃ n : ℕ, algebraMap S (Localization.Away g) a ^ n * (t : Amb f g q).2 k = 0) :
    ∃ N : ℕ, a ^ N * s t = 0 := by
  choose n1 hn1 using h1
  choose n2 hn2 using h2
  refine ⟨∑ k, (n1 k + n2 k), ?_⟩
  have hle : ∀ k, n1 k + n2 k ≤ ∑ k, (n1 k + n2 k) := fun k =>
    Finset.single_le_sum (f := fun k => n1 k + n2 k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hz : torMap f g hε (a ^ ∑ k, (n1 k + n2 k)) * t = 0 := by
    apply Subtype.ext
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show algebraMap S _ (a ^ ∑ k, (n1 k + n2 k)) * (t : Amb f g q).1 k = 0
      rw [map_pow, ← Nat.sub_add_cancel ((Nat.le_add_right _ _).trans (hle k)), pow_add, mul_assoc, hn1 k, mul_zero]
    · show algebraMap S _ (a ^ ∑ k, (n1 k + n2 k)) * (t : Amb f g q).2 k = 0
      rw [map_pow, ← Nat.sub_add_cancel ((Nat.le_add_left _ _).trans (hle k)), pow_add, mul_assoc, hn2 k, mul_zero]
  have := congrArg s hz
  rwa [map_mul, hs, map_zero] at this

lemma killF (s : Tor f g hε →+* S) (hs : ∀ a, s (torMap f g hε a) = a) (t : Tor f g hε)
    (h0 : (t : Amb f g q).1 = 0) : algebraMap S (Localization.Away f) (s t) = 0 := by
  have htor := (mem_tor hε _).1 t.2
  have hz : ∀ m, rR f g ((t : Amb f g q).2 m) = 0 := twist_inj hε (fun m => rR f g ((t : Amb f g q).2 m))
    (fun k => by
      show ∑ c, ε c * rR f g ((t : Amb f g q).2 (k + c)) = 0
      rw [← htor k, h0, Pi.zero_apply, map_zero])
  obtain ⟨N, hN⟩ := kill hε s hs t f (fun k => ⟨0, by rw [h0]; simp⟩)
    (fun k => loc_ker g f (mul_comm g f) (rR f g) rR_alg _ (hz k))
  have := congrArg (algebraMap S (Localization.Away f)) hN
  rw [map_mul, map_pow, map_zero] at this
  exact ((IsLocalization.Away.algebraMap_isUnit f).pow N).mul_right_eq_zero.1 this

lemma killG (s : Tor f g hε →+* S) (hs : ∀ a, s (torMap f g hε a) = a) (t : Tor f g hε)
    (h0 : (t : Amb f g q).2 = 0) : algebraMap S (Localization.Away g) (s t) = 0 := by
  have htor := (mem_tor hε _).1 t.2
  have hz : ∀ k, rL f g ((t : Amb f g q).1 k) = 0 := fun k => by rw [htor k, h0]; simp
  obtain ⟨N, hN⟩ := kill hε s hs t g (fun k => loc_ker f g rfl (rL f g) rL_alg _ (hz k))
    (fun k => ⟨0, by rw [h0]; simp⟩)
  have := congrArg (algebraMap S (Localization.Away g)) hN
  rw [map_mul, map_pow, map_zero] at this
  exact ((IsLocalization.Away.algebraMap_isUnit g).pow N).mul_right_eq_zero.1 this

lemma liftF (k : ZMod q) : ∃ (N : ℕ) (t : Tor f g hε),
    (t : Amb f g q).1 = Pi.single k (algebraMap S (Localization.Away f) f ^ N) := by
  classical
  let x : ZMod q → Localization.Away f := Pi.single k 1
  let w : ZMod q → Localization.Away (f * g) := fun m => ∑ d, ε d * rL f g (x (m - d))
  have hw : ∀ j, ∑ c, ε c * w (j + c) = rL f g (x j) := fun j => twist_inv hε (fun i => rL f g (x i)) j
  choose n y hy using fun m => loc_surj g f (mul_comm g f) (rR f g) rR_alg (w m)
  have hle : ∀ m, n m ≤ ∑ m, n m := fun m => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  let y' : ZMod q → Localization.Away g := fun m => algebraMap S _ f ^ (∑ m, n m - n m) * y m
  have hy' : ∀ m, rR f g (y' m) = algebraMap S _ f ^ (∑ m, n m) * w m := by
    intro m
    simp only [y', map_mul, map_pow, rR_alg, ← hy m]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle m)]
  have hmem : ((fun j => algebraMap S _ f ^ (∑ m, n m) * x j, y') : Amb f g q) ∈ Tor f g hε := by
    rw [mem_tor]
    intro j
    simp only [hy', map_mul, map_pow, rL_alg]
    rw [← hw j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  refine ⟨∑ m, n m, ⟨_, hmem⟩, ?_⟩
  funext j
  show algebraMap S _ f ^ (∑ m, n m) * x j = _
  by_cases h : j = k
  · subst h; simp [x]
  · simp [x, Pi.single_apply, h]

lemma liftG (k : ZMod q) : ∃ (N : ℕ) (t : Tor f g hε),
    (t : Amb f g q).2 = Pi.single k (algebraMap S (Localization.Away g) g ^ N) := by
  classical
  let y : ZMod q → Localization.Away g := Pi.single k 1
  let v : ZMod q → Localization.Away (f * g) := fun j => ∑ c, ε c * rR f g (y (j + c))
  choose n x hx using fun j => loc_surj f g rfl (rL f g) rL_alg (v j)
  have hle : ∀ m, n m ≤ ∑ m, n m := fun m => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  let x' : ZMod q → Localization.Away f := fun m => algebraMap S _ g ^ (∑ m, n m - n m) * x m
  have hx' : ∀ m, rL f g (x' m) = algebraMap S _ g ^ (∑ m, n m) * v m := by
    intro m
    simp only [x', map_mul, map_pow, rL_alg, ← hx m]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle m)]
  have hmem : ((x', fun j => algebraMap S _ g ^ (∑ m, n m) * y j) : Amb f g q) ∈ Tor f g hε := by
    rw [mem_tor]
    intro j
    simp only [hx', map_mul, map_pow, rR_alg, v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  refine ⟨∑ m, n m, ⟨_, hmem⟩, ?_⟩
  funext j
  show algebraMap S _ g ^ (∑ m, n m) * y j = _
  by_cases h : j = k
  · subst h; simp [y]
  · simp [y, Pi.single_apply, h]
end Main

section IF
variable {q : ℕ} [NeZero q]

lemma idem_family {B : Type} [CommRing B] (F : B) (hF : IsUnit F) (N : ℕ) (σ : ZMod q → B)
    (h1 : ∀ k, σ k * σ k = F ^ N * σ k) (h2 : ∀ j k, j ≠ k → σ j * σ k = 0) (h3 : ∑ k, σ k = F ^ N) :
    ∃ δ : ZMod q → B, CompleteOrthogonalIdempotents δ ∧ ∀ k, σ k = F ^ N * δ k := by
  obtain ⟨u, rfl⟩ := hF
  refine ⟨fun k => σ k * (↑u⁻¹ : B) ^ N, { idem := fun k => ?_, ortho := fun j k hjk => ?_, complete := ?_ }, fun k => ?_⟩
  · show σ k * (↑u⁻¹ : B) ^ N * (σ k * (↑u⁻¹ : B) ^ N) = σ k * (↑u⁻¹ : B) ^ N
    calc _ = (σ k * σ k) * (↑u⁻¹ : B) ^ N * (↑u⁻¹ : B) ^ N := by ring
      _ = σ k * ((↑u : B) * ↑u⁻¹) ^ N * (↑u⁻¹ : B) ^ N := by rw [h1]; ring
      _ = _ := by rw [Units.mul_inv, one_pow, mul_one]
  · show σ j * (↑u⁻¹ : B) ^ N * (σ k * (↑u⁻¹ : B) ^ N) = 0
    calc _ = (σ j * σ k) * (↑u⁻¹ : B) ^ N * (↑u⁻¹ : B) ^ N := by ring
      _ = 0 := by rw [h2 j k hjk]; ring
  · rw [← Finset.sum_mul, h3, ← mul_pow, Units.mul_inv, one_pow]
  · show σ k = (↑u : B) ^ N * (σ k * (↑u⁻¹ : B) ^ N)
    calc σ k = σ k * ((↑u : B) * ↑u⁻¹) ^ N := by rw [Units.mul_inv, one_pow, mul_one]
      _ = _ := by ring

end IF

section Sheets
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] {f g : S} {ε : ZMod q → Localization.Away (f * g)}
  (hε : CompleteOrthogonalIdempotents ε)
include hε

lemma uniformF : ∃ (N : ℕ) (t : ZMod q → Tor f g hε),
    ∀ k, (t k : Amb f g q).1 = Pi.single k (algebraMap S (Localization.Away f) f ^ N) := by
  classical
  choose n t ht using liftF hε (f := f) (g := g)
  have hle : ∀ m, n m ≤ ∑ m, n m := fun m => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  refine ⟨∑ m, n m, fun k => torMap f g hε (f ^ (∑ m, n m - n k)) * t k, fun k => ?_⟩
  funext i
  show algebraMap S _ (f ^ (∑ m, n m - n k)) * (t k : Amb f g q).1 i = _
  rw [ht k]
  by_cases h : i = k
  · subst h; simp only [Pi.single_eq_same, map_pow]; rw [← pow_add, Nat.sub_add_cancel (hle i)]
  · simp [Pi.single_apply, h]

lemma uniformG : ∃ (N : ℕ) (t : ZMod q → Tor f g hε),
    ∀ k, (t k : Amb f g q).2 = Pi.single k (algebraMap S (Localization.Away g) g ^ N) := by
  classical
  choose n t ht using liftG hε (f := f) (g := g)
  have hle : ∀ m, n m ≤ ∑ m, n m := fun m => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  refine ⟨∑ m, n m, fun k => torMap f g hε (g ^ (∑ m, n m - n k)) * t k, fun k => ?_⟩
  funext i
  show algebraMap S _ (g ^ (∑ m, n m - n k)) * (t k : Amb f g q).2 i = _
  rw [ht k]
  by_cases h : i = k
  · subst h; simp only [Pi.single_eq_same, map_pow]; rw [← pow_add, Nat.sub_add_cancel (hle i)]
  · simp [Pi.single_apply, h]

lemma coe_sum_tor (t : ZMod q → Tor f g hε) : ((∑ k, t k : Tor f g hε) : Amb f g q) = ∑ k, (t k : Amb f g q) :=
  map_sum (Tor f g hε).subtype _ _

lemma sheetF (s : Tor f g hε →+* S) (hs : ∀ a, s (torMap f g hε a) = a) :
    ∃ (N : ℕ) (t : ZMod q → Tor f g hε) (δ : ZMod q → Localization.Away f), CompleteOrthogonalIdempotents δ ∧
      (∀ k, (t k : Amb f g q).1 = Pi.single k (algebraMap S (Localization.Away f) f ^ N)) ∧
      ∀ k, algebraMap S _ (s (t k)) = algebraMap S (Localization.Away f) f ^ N * δ k := by
  classical
  obtain ⟨N, t, ht⟩ := uniformF hε (f := f) (g := g)
  have hs' : ∀ x : Tor f g hε, (x : Amb f g q).1 = 0 → algebraMap S (Localization.Away f) (s x) = 0 := killF hε s hs
  obtain ⟨δ, hδ, hσ⟩ := idem_family (algebraMap S (Localization.Away f) f) (IsLocalization.Away.algebraMap_isUnit f) N
    (fun k => algebraMap S _ (s (t k)))
    (fun k => by
      have := hs' (t k * t k - torMap f g hε (f ^ N) * t k) (by
        show (t k : Amb f g q).1 * (t k : Amb f g q).1 - (fun _ => algebraMap S _ (f ^ N)) * (t k : Amb f g q).1 = 0
        rw [ht k]; funext i; by_cases h : i = k <;> simp [Pi.single_apply, h])
      rw [map_sub, map_mul, map_mul, hs, map_sub, map_mul, map_mul, map_pow, sub_eq_zero] at this
      exact this)
    (fun j k hjk => by
      have := hs' (t j * t k) (by
        show (t j : Amb f g q).1 * (t k : Amb f g q).1 = 0
        rw [ht j, ht k]; funext i
        by_cases h : i = j
        · subst h; simp [Pi.single_apply, hjk]
        · simp [Pi.single_apply, h])
      rwa [map_mul, map_mul] at this)
    (by
      have := hs' (∑ k, t k - torMap f g hε (f ^ N)) (by
        show ((∑ k, t k : Tor f g hε) : Amb f g q).1 - (fun _ => algebraMap S _ (f ^ N)) = 0
        rw [coe_sum_tor, Prod.fst_sum]; simp only [ht]; funext i
        simp [Finset.sum_apply, Pi.single_apply])
      rw [map_sub, hs, map_sub, map_sum, map_sum, map_pow, sub_eq_zero] at this
      exact this)
  exact ⟨N, t, δ, hδ, ht, hσ⟩

lemma sheetG (s : Tor f g hε →+* S) (hs : ∀ a, s (torMap f g hε a) = a) :
    ∃ δ : ZMod q → Localization.Away g, CompleteOrthogonalIdempotents δ ∧
      ∀ (x : Tor f g hε) m, algebraMap S _ (s x) * δ m = (x : Amb f g q).2 m * δ m := by
  classical
  obtain ⟨N, t, ht⟩ := uniformG hε (f := f) (g := g)
  have hs' : ∀ x : Tor f g hε, (x : Amb f g q).2 = 0 → algebraMap S (Localization.Away g) (s x) = 0 := killG hε s hs
  obtain ⟨δ, hδ, hσ⟩ := idem_family (algebraMap S (Localization.Away g) g) (IsLocalization.Away.algebraMap_isUnit g) N
    (fun k => algebraMap S _ (s (t k)))
    (fun k => by
      have := hs' (t k * t k - torMap f g hε (g ^ N) * t k) (by
        show (t k : Amb f g q).2 * (t k : Amb f g q).2 - (fun _ => algebraMap S _ (g ^ N)) * (t k : Amb f g q).2 = 0
        rw [ht k]; funext i; by_cases h : i = k <;> simp [Pi.single_apply, h])
      rw [map_sub, map_mul, map_mul, hs, map_sub, map_mul, map_mul, map_pow, sub_eq_zero] at this
      exact this)
    (fun j k hjk => by
      have := hs' (t j * t k) (by
        show (t j : Amb f g q).2 * (t k : Amb f g q).2 = 0
        rw [ht j, ht k]; funext i
        by_cases h : i = j
        · subst h; simp [Pi.single_apply, hjk]
        · simp [Pi.single_apply, h])
      rwa [map_mul, map_mul] at this)
    (by
      have := hs' (∑ k, t k - torMap f g hε (g ^ N)) (by
        show ((∑ k, t k : Tor f g hε) : Amb f g q).2 - (fun _ => algebraMap S _ (g ^ N)) = 0
        rw [coe_sum_tor, Prod.snd_sum]; simp only [ht]; funext i
        simp [Finset.sum_apply, Pi.single_apply])
      rw [map_sub, hs, map_sub, map_sum, map_sum, map_pow, sub_eq_zero] at this
      exact this)
  refine ⟨δ, hδ, fun x m => ?_⟩
  obtain ⟨j, b, hb⟩ := IsLocalization.Away.surj g ((x : Amb f g q).2 m)
  have e1 := hs' (torMap f g hε (g ^ j) * x * t m - torMap f g hε b * t m) (by
    show (fun _ => algebraMap S _ (g ^ j)) * (x : Amb f g q).2 * (t m : Amb f g q).2
      - (fun _ => algebraMap S _ b) * (t m : Amb f g q).2 = 0
    rw [ht m]; funext i
    by_cases h : i = m
    · subst h; simp only [Pi.sub_apply, Pi.mul_apply, Pi.single_eq_same, Pi.zero_apply, map_pow, ← hb]; ring
    · simp [Pi.single_apply, h])
  simp only [map_sub, map_mul, hs, map_pow] at e1
  rw [hσ m] at e1
  have hu : IsUnit (algebraMap S (Localization.Away g) g ^ j * algebraMap S (Localization.Away g) g ^ N) :=
    ((IsLocalization.Away.algebraMap_isUnit g).pow j).mul ((IsLocalization.Away.algebraMap_isUnit g).pow N)
  apply hu.mul_left_cancel
  linear_combination e1 - (algebraMap S (Localization.Away g) g ^ N * δ m) * hb
end Sheets

theorem TorSec_of : TorSec := by
  rintro q _ S _ f g _hfg φ ε hε hφ
  letI := (torMap f g hε).toAlgebra
  rintro ⟨s⟩
  have hs : ∀ a, s.toRingHom (torMap f g hε a) = a := fun a => s.commutes a
  obtain ⟨N, t, δ, hδ, ht, hσ⟩ := sheetF hε s.toRingHom hs
  obtain ⟨δ', hδ', hev⟩ := sheetG hε s.toRingHom hs
  refine ⟨-lcOf hδ, -lcOf hδ', ?_⟩
  ext P
  show φ P = -(lcOf hδ (PrimeSpectrum.comap (rL f g) P)) - -(lcOf hδ' (PrimeSpectrum.comap (rR f g) P))
  have hk0 : rL f g (δ (lcOf hδ (PrimeSpectrum.comap (rL f g) P))) ∉ P.asIdeal := fun h =>
    lcOf_spec hδ (PrimeSpectrum.comap (rL f g) P) (by rw [PrimeSpectrum.comap_asIdeal]; exact h)
  have hm0 : rR f g (δ' (lcOf hδ' (PrimeSpectrum.comap (rR f g) P))) ∉ P.asIdeal := fun h =>
    lcOf_spec hδ' (PrimeSpectrum.comap (rR f g) P) (by rw [PrimeSpectrum.comap_asIdeal]; exact h)
  generalize lcOf hδ (PrimeSpectrum.comap (rL f g) P) = k0 at hk0 ⊢
  generalize lcOf hδ' (PrimeSpectrum.comap (rR f g) P) = m0 at hm0 ⊢
  have hc0 : ε (φ P) ∉ P.asIdeal := (hφ P (φ P)).1 rfl
  suffices h : k0 = m0 - φ P by rw [h]; ring
  by_contra hne
  have htor := (mem_tor hε _).1 (t k0).2 (m0 - φ P)
  rw [ht k0, Pi.single_apply, if_neg (Ne.symm hne), map_zero] at htor
  have h1 : ε (φ P) * rR f g ((t k0 : Amb f g q).2 m0) = 0 := by
    have := congrArg (ε (φ P) * ·) htor
    simp only [mul_zero] at this
    rw [eps_mul_sum hε, sub_add_cancel] at this
    exact this.symm
  have h2 : rR f g ((t k0 : Amb f g q).2 m0) ∈ P.asIdeal :=
    (P.isPrime.mem_or_mem (by rw [h1]; exact P.asIdeal.zero_mem)).resolve_left hc0
  have h3 : rR f g (algebraMap S _ (s.toRingHom (t k0))) ∈ P.asIdeal := by
    have : rR f g (algebraMap S _ (s.toRingHom (t k0))) * rR f g (δ' m0) ∈ P.asIdeal := by
      rw [← map_mul, hev, map_mul]; exact P.asIdeal.mul_mem_right _ h2
    exact (P.isPrime.mem_or_mem this).resolve_right hm0
  have h4 : rL f g (algebraMap S _ (s.toRingHom (t k0))) ∈ P.asIdeal := by
    rw [rL_alg]; rwa [rR_alg] at h3
  rw [hσ k0, map_mul, map_pow, rL_alg] at h4
  have hu : IsUnit (algebraMap S (Localization.Away (f * g)) f) :=
    isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g))
  rcases P.isPrime.mem_or_mem h4 with h | h
  · exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu.pow N))
  · exact hk0 h

end LateralTheory.E.TorSecPf

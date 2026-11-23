import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

section Frob

variable {l : ℕ} {R : Type} [CommRing R] (φ : R →+* R)

theorem mem_span_of_frob_mem (hb : Function.Bijective φ) {y p : R}
    (h : φ y ∈ Ideal.span {φ p}) : y ∈ Ideal.span {p} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨c', rfl⟩ := hb.2 c
  exact Ideal.mem_span_singleton'.2 ⟨c', hb.1 (by rw [map_mul, hc])⟩

theorem mem_span_of_pow_mem (hφ : ∀ x, φ x = x ^ l) (hb : Function.Bijective φ) {x p : R}
    (N : ℕ) (h : x ^ l ^ N ∈ Ideal.span {p ^ l ^ N}) : x ∈ Ideal.span {p} := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih (mem_span_of_frob_mem φ hb ?_)
    rw [hφ, hφ, ← pow_mul, ← pow_mul, ← pow_succ]
    exact h

theorem sub_pow_of_frob (hφ : ∀ x, φ x = x ^ l) (a b : R) (N : ℕ) :
    (a - b) ^ l ^ N = a ^ l ^ N - b ^ l ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih, ← hφ, map_sub, hφ, hφ]

end Frob

theorem root_pow {l : ℕ} {T : Type} [Monoid T] {x : ℕ → T} (hx : ∀ m, x (m + 1) ^ l = x m) (m k : ℕ) :
    x (m + k) ^ l ^ k = x m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' l k, pow_mul, ← add_assoc, hx, ih]

variable {l : ℕ} [Fact l.Prime]

def powSum (A : PAlg l) (u : (A.cont ℤ_[l]).A) (N : ℕ) : (A.cont ℤ_[l]).A :=
  ∑ c : ZMod (l ^ N), ind A N c * u ^ c.val

theorem ev_powSum (A : PAlg l) (u : (A.cont ℤ_[l]).A) (N : ℕ) (z : ℤ_[l]) :
    Hom.f (A.evCont z) (powSum A u N) = Hom.f (A.evCont z) u ^ (PadicInt.toZModPow N z).val := by
  rw [powSum, map_sum]
  simp only [map_mul, map_pow, ev_ind, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem sub_powSum_mem (A : PAlg l) {u ρ : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (hρ : ∀ n, ρ (n + 1) ^ l = ρ n)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) (ρ 0) -
      Hom.f (A.evCont z) (u 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {A.pi ^ (l ^ m)})
    (N : ℕ) : ρ N - powSum A (u N) N ∈ Ideal.span {(A.cont ℤ_[l]).pi} := by
  have hf : ∀ x : (A.cont ℤ_[l]).A, (A.cont ℤ_[l]).frob x = x ^ l := fun _ => rfl
  refine mem_span_of_pow_mem (l := l) (A.cont ℤ_[l]).frob hf (A.cont ℤ_[l]).frob_bijective N ?_
  have h1 : ρ N ^ l ^ N = ρ 0 := by simpa using root_pow hρ 0 N
  have h2 : u N ^ l ^ N = u 0 := by simpa using root_pow hu 0 N
  rw [sub_pow_of_frob (l := l) _ hf, h1, mem_span_pi_pow]
  intro z
  rw [map_sub, map_pow, ev_powSum, ← pow_mul, mul_comm, pow_mul, ← map_pow, h2]
  exact h0 N z

theorem sharp_powSum (A : PAlg l) {u : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (m k : ℕ) (hv : (A.cont ℤ_[l]).sharp (u m) ^ l ^ m = 1) :
    (A.cont ℤ_[l]).sharp (powSum A (u (m + k)) (m + k) ^ l ^ k) =
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val := by
  set B := powSum A (u (m + k)) (m + k) ^ l ^ k with hB
  set v := (A.cont ℤ_[l]).sharp (u m) with hvdef
  set T := ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * v ^ c.val with hT
  have hle : m ≤ m + k := Nat.le_add_right m k
  have h1 : ∀ c' : ZMod (l ^ (m + k)), ind A (m + k) c' * B = ind A (m + k) c' * u m ^ c'.val := by
    intro c'
    refine cont_ext fun z => ?_
    rw [map_mul, map_mul, ev_ind]
    split_ifs with h
    · have hr : Hom.f (A.evCont z) (u (m + k)) ^ l ^ k = Hom.f (A.evCont z) (u m) := by
        rw [← map_pow, root_pow hu]
      rw [hB, map_pow, ev_powSum, map_pow, h, ← pow_mul, mul_comm c'.val, pow_mul, hr]
    · simp
  have h2 : ∀ (c' : ZMod (l ^ (m + k))) (c : ZMod (l ^ m)), ZMod.cast c' ≠ c →
      ind A (m + k) c' * ind A m c = 0 := by
    intro c' c hc
    refine cont_ext fun z => ?_
    rw [map_mul, ev_ind, ev_ind, map_zero]
    split_ifs with h h'
    · exact absurd (by rw [← h', ← h, PadicInt.cast_toZModPow m (m + k) hle]) hc
    all_goals simp
  have h3 : ∀ c' : ZMod (l ^ (m + k)),
      ind A (m + k) c' * ind A m (ZMod.cast c') = ind A (m + k) c' := by
    intro c'
    refine cont_ext fun z => ?_
    rw [map_mul, ev_ind, ev_ind]
    split_ifs with h h'
    · simp
    · exact absurd (by rw [← h, PadicInt.cast_toZModPow m (m + k) hle]) h'
    all_goals simp
  have h4 : ∀ c' : ZMod (l ^ (m + k)), v ^ (ZMod.cast c' : ZMod (l ^ m)).val = v ^ c'.val := by
    intro c'
    rw [pow_eq_pow_mod c'.val hv, ← ZMod.natCast_val, ZMod.val_natCast]
  have key : ∀ c' : ZMod (l ^ (m + k)), (A.cont ℤ_[l]).sharp (ind A (m + k) c') * (A.cont ℤ_[l]).sharp B =
      (A.cont ℤ_[l]).sharp (ind A (m + k) c') * T := by
    intro c'
    rw [← map_mul, h1, map_mul, map_pow, hT, Finset.mul_sum, Finset.sum_eq_single (ZMod.cast c')]
    · rw [← mul_assoc, ← map_mul, h3, h4]
    · intro c _ hc
      rw [← mul_assoc, ← map_mul, h2 c' c (Ne.symm hc), sharp_zero, zero_mul]
    · simp
  have hsum := sum_sharp_eq_one (A.cont ℤ_[l]) (coi_ind A (m + k))
  calc (A.cont ℤ_[l]).sharp B = (∑ c', (A.cont ℤ_[l]).sharp (ind A (m + k) c')) * (A.cont ℤ_[l]).sharp B := by
        rw [hsum, one_mul]
    _ = (∑ c', (A.cont ℤ_[l]).sharp (ind A (m + k) c')) * T := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c' _ => key c'
    _ = T := by rw [hsum, one_mul]

theorem sharp_roots_core (A : PAlg l) {u ρ : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (hs : (A.cont ℤ_[l]).sharp (u 0) = 1) (hρ : ∀ n, ρ (n + 1) ^ l = ρ n)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) (ρ 0) -
      Hom.f (A.evCont z) (u 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {A.pi ^ (l ^ m)})
    (m : ℕ) : (A.cont ℤ_[l]).sharp (ρ m) =
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val := by
  have hv : (A.cont ℤ_[l]).sharp (u m) ^ l ^ m = 1 := by
    rw [← map_pow, (by simpa using root_pow hu 0 m : u m ^ l ^ m = u 0), hs]
  have hk : ∀ k, (A.cont ℤ_[l]).sharp (ρ m) -
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val ∈
      Ideal.span {(l : (A.cont ℤ_[l]).U) ^ (k + 1)} := by
    intro k
    have h := (RL.sharp_cong (A.cont ℤ_[l])).1 _ _ k (sub_powSum_mem A hu hρ h0 (m + k))
    rwa [root_pow hρ, sharp_powSum A hu m k hv] at h
  refine sub_eq_zero.1 (IsHausdorff.haus
    (inferInstance : IsHausdorff (Ideal.span {(l : (A.cont ℤ_[l]).U)}) (A.cont ℤ_[l]).U) _ fun k => ?_)
  refine smodEq_iff.2 ?_
  rw [sub_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hk k)
  exact Ideal.mem_span_singleton'.2 ⟨c * l, by rw [← hc, pow_succ]; ring⟩

theorem sharp_roots_universal {l : ℕ} [Fact l.Prime] (ε : Eps l) (ρ : ℕ → ((base l).cont ℤ_[l]).A)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) (ρ 0) -
      (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)})
    (hρ : ∀ m, ρ (m + 1) ^ l = ρ m) (m : ℕ) : ((base l).cont ℤ_[l]).sharp (ρ m) =
    ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (GlobalTheory.CompanionTheory.ContUniv.ind (base l) m c) *
      ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val := by
  have hev : ∀ (n : ℕ) (z : ℤ_[l]),
      Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e n)) = (base l).s (ε.e n) :=
    fun n z => RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
  refine sharp_roots_core (base l) (u := fun n => ((base l).cont ℤ_[l]).s (ε.e n)) (fun n => ?_)
    (ε.sharp_e _) hρ (fun k z => ?_) m
  · show ((base l).cont ℤ_[l]).s (ε.e (n + 1)) ^ l = ((base l).cont ℤ_[l]).s (ε.e n)
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]
  · show Hom.f ((base l).evCont z) (ρ 0) -
      Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) ^ _ ∈ _
    rw [hev]
    exact h0 k z

end GlobalTheory.CompanionTheory.ContUniv

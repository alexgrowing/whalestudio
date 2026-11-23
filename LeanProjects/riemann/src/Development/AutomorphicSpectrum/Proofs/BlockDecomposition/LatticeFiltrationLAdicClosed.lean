import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLTorsionFreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPowStatement

set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatClosed

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def T (r : ℕ) : AddSubgroup B :=
  AddSubgroup.closure {b | ∃ (w : W) (i : ℕ), r ≤ i ∧ b = f w * Lat.dpE f ξ l M i}

theorem dpE_eq (i : ℕ) : Lat.dpE f ξ l M i =
    (((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ i := by
  simp only [Lat.dpE, Lat.η, smul_pow, smul_smul]

theorem dpE_mem {r i : ℕ} (h : r ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ r} := by
  rw [dpE_eq, Algebra.smul_def, Ideal.mem_span_singleton]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ h) _

theorem mul_dpE (hl : l ≠ 0) (r : ℕ) : f ξ * Lat.dpE f ξ l M r =
    f ((l : W) ^ M * ((r + 1 : ℕ) : W)) * Lat.dpE f ξ l M (r + 1) := by
  have hl' : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hf : ((r.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
  have hr : ((r + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)
  have key : ((r.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ r =
      (((l ^ M * (r + 1) : ℕ)) : ℚ) * (((r + 1).factorial : ℚ)⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ (r + 1)) := by
    rw [Nat.factorial_succ]
    push_cast at hr ⊢
    have hu : (l : ℚ) ^ M * ((l : ℚ) ^ M)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hl')
    generalize ((l : ℚ) ^ M)⁻¹ = u at hu ⊢
    field_simp
    rw [pow_succ]
    linear_combination (-(u ^ r)) * hu
  rw [dpE_eq, dpE_eq, key, Algebra.smul_def, Algebra.smul_def, map_mul, map_natCast]
  simp only [map_mul, map_pow, map_natCast]
  push_cast
  ring

theorem T_split (r : ℕ) {b : B} (hb : b ∈ T f ξ l M r) :
    ∃ c : W, ∃ t ∈ T f ξ l M (r + 1), b = f c * Lat.dpE f ξ l M r + t := by
  induction hb using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hi, rfl⟩ := hx
    rcases hi.eq_or_lt with rfl | hlt
    · exact ⟨w, 0, zero_mem _, by simp⟩
    · exact ⟨0, _, AddSubgroup.subset_closure ⟨w, i, hlt, rfl⟩, by simp⟩
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, t, ht, rfl⟩ := hx
    obtain ⟨c', t', ht', rfl⟩ := hy
    exact ⟨c + c', t + t', add_mem ht ht', by rw [map_add]; ring⟩
  | neg x _ hx =>
    obtain ⟨c, t, ht, rfl⟩ := hx
    exact ⟨-c, -t, neg_mem ht, by rw [map_neg]; ring⟩

theorem T_mem_span {r : ℕ} {b : B} (hb : b ∈ T f ξ l M r) : b ∈ Ideal.span {f ξ ^ r} := by
  induction hb using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hi, rfl⟩ := hx
    exact Ideal.mul_mem_left _ _ (dpE_mem f ξ l M hi)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem mem_T_zero {b : B} (hb : b ∈ Lat.sub f ξ l M) : b ∈ T f ξ l M 0 := by
  obtain ⟨n, c, rfl⟩ := (GlobalTheory.T.mem_lattice_sub_iff_sum f ξ l M b).1 hb
  exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, i, Nat.zero_le _, rfl⟩

theorem xi_mul_mem (hl : l ≠ 0) (r : ℕ) (e : W) :
    f (ξ * e) * Lat.dpE f ξ l M r ∈ T f ξ l M (r + 1) := by
  refine AddSubgroup.subset_closure ⟨e * ((l : W) ^ M * ((r + 1 : ℕ) : W)), r + 1, le_rfl, ?_⟩
  rw [map_mul, map_mul f e, mul_assoc (f e), ← mul_dpE f ξ l M hl r]
  ring

variable {f ξ l M}

theorem l_ne_zero {m : ℕ} (h : Lat.Hyp f ξ l m) : l ≠ 0 := fun h0 => h.l0 (by simp [h0])

theorem dvd_of_mem {m r : ℕ} (h : Lat.Hyp f ξ l m) (hr : r < m) {c : W}
    (hc : f c * Lat.dpE f ξ l M r ∈ Ideal.span {f ξ ^ (r + 1)}) : ξ ∣ c := by
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (l_ne_zero h)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hc
  set s : ℚ := ((r.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ r with hs
  have hs0 : s ≠ 0 := by
    have : ((r.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
    rw [hs]; positivity
  rw [dpE_eq, ← hs] at hb
  refine h.gr r hr c (s⁻¹ • b) ?_
  have : s⁻¹ • (f c * s • f ξ ^ r) = s⁻¹ • (f ξ ^ (r + 1) * b) := by rw [hb]
  rwa [mul_smul_comm, smul_smul, inv_mul_cancel₀ hs0, one_smul, ← mul_smul_comm] at this

theorem T_of_span {m : ℕ} (h : Lat.Hyp f ξ l m) (r : ℕ) {b : B} (h0 : b ∈ T f ξ l M 0)
    (hb : b ∈ Ideal.span {f ξ ^ r}) : b ∈ T f ξ l M r := by
  induction r with
  | zero => exact h0
  | succ r ih =>
    have hr : b ∈ T f ξ l M r :=
      ih (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ r)) hb)
    by_cases hrm : r < m
    · obtain ⟨c, t, ht, rfl⟩ := T_split f ξ l M r hr
      have hc : f c * Lat.dpE f ξ l M r ∈ Ideal.span {f ξ ^ (r + 1)} := by
        have := sub_mem hb (T_mem_span f ξ l M ht)
        rwa [add_sub_cancel_right] at this
      obtain ⟨e, rfl⟩ := dvd_of_mem h hrm hc
      exact add_mem (xi_mul_mem f ξ l M (l_ne_zero h) r e) ht
    · have hz : f ξ ^ (r + 1) = 0 := pow_eq_zero_of_le (by omega) h.nil
      rw [hz, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at hb
      rw [hb]; exact zero_mem _

theorem tf_pow {m : ℕ} (h : Lat.Hyp f ξ l m) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (r n : ℕ)
    (a : Lat.A f ξ l M) (H : (l : Lat.A f ξ l M) ^ n * a ∈ pdP (Lat.γ f ξ l M hc) r) :
    a ∈ pdP (Lat.γ f ξ l M hc) r := by
  induction n with
  | zero => simpa using H
  | succ n ih =>
    rw [pow_succ', mul_assoc] at H
    exact ih (GlobalTheory.T.lattice_filtration_l_torsion_free f ξ l M m h hc r _ H)

theorem lat_ι_mem_T_zero (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ T f ξ l M 0 :=
  mem_T_zero f ξ l M (Subtype.prop x)

theorem closed_succ {m : ℕ} (h : Lat.Hyp f ξ l m) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (r : ℕ)
    (ih : ∀ x : Lat.A f ξ l M, (∀ n : ℕ, x ∈ Ideal.span {(l : Lat.A f ξ l M) ^ n} ⊔ pdP (Lat.γ f ξ l M hc) r) →
      x ∈ pdP (Lat.γ f ξ l M hc) r)
    (x : Lat.A f ξ l M)
    (hx : ∀ n : ℕ, x ∈ Ideal.span {(l : Lat.A f ξ l M) ^ n} ⊔ pdP (Lat.γ f ξ l M hc) (r + 1)) :
    x ∈ pdP (Lat.γ f ξ l M hc) (r + 1) := by
  have E := GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc
  have hle : pdP (Lat.γ f ξ l M hc) (r + 1) ≤ pdP (Lat.γ f ξ l M hc) r := by
    rw [E, E]
    exact Ideal.comap_mono (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ r)))
  have hxr : x ∈ pdP (Lat.γ f ξ l M hc) r := ih x fun n => sup_le_sup_left hle _ (hx n)
  have hxr' : Lat.ι f ξ l M x ∈ Ideal.span {f ξ ^ r} := by
    rw [E] at hxr; exact hxr
  by_cases hrm : r < m
  · obtain ⟨c, t, ht, hcx⟩ := T_split f ξ l M r (T_of_span h r (lat_ι_mem_T_zero x) hxr')
    have hz : Ideal.Quotient.mk (Ideal.span {ξ}) c = 0 := by
      refine h.cpl.toIsHausdorff.haus' _ fun n => ?_
      obtain ⟨a, y, hy, hxa⟩ := Ideal.mem_span_singleton_sup.1 (hx n)
      have hay : (l : Lat.A f ξ l M) ^ n * a ∈ pdP (Lat.γ f ξ l M hc) r := by
        have : (l : Lat.A f ξ l M) ^ n * a = x - y := by rw [← hxa]; ring
        rw [this]; exact sub_mem hxr (hle hy)
      have ha := tf_pow h hc r n a hay
      have ha' : Lat.ι f ξ l M a ∈ Ideal.span {f ξ ^ r} := by
        rw [E] at ha; exact ha
      obtain ⟨d, t', ht', hda⟩ := T_split f ξ l M r (T_of_span h r (lat_ι_mem_T_zero a) ha')
      have hy' : Lat.ι f ξ l M y ∈ Ideal.span {f ξ ^ (r + 1)} := by
        rw [E] at hy; exact hy
      have hxa' : Lat.ι f ξ l M a * (l : B) ^ n + Lat.ι f ξ l M y = Lat.ι f ξ l M x := by
        rw [← hxa]; simp only [map_add, map_mul, map_pow, map_natCast]
      have e : f (c - (l : W) ^ n * d) * Lat.dpE f ξ l M r =
          (l : B) ^ n * t' + Lat.ι f ξ l M y - t := by
        simp only [map_sub, map_mul, map_pow, map_natCast]
        linear_combination (-1) * hcx - hxa' + (l : B) ^ n * hda
      have hm : f (c - (l : W) ^ n * d) * Lat.dpE f ξ l M r ∈ Ideal.span {f ξ ^ (r + 1)} := by
        rw [e]
        exact sub_mem (add_mem (Ideal.mul_mem_left _ _ (T_mem_span f ξ l M ht')) hy') (T_mem_span f ξ l M ht)
      have hdv := dvd_of_mem h hrm hm
      have heq : Ideal.Quotient.mk (Ideal.span {ξ}) c = Ideal.Quotient.mk (Ideal.span {ξ}) ((l : W) ^ n * d) :=
        Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hdv)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact ⟨Ideal.Quotient.mk _ d, by rw [heq, map_mul, map_pow, map_natCast]⟩
    obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hz)
    rw [E, Ideal.mem_comap, hcx]
    exact T_mem_span f ξ l M (add_mem (xi_mul_mem f ξ l M (l_ne_zero h) r e) ht)
  · have h0 : f ξ ^ r = 0 := pow_eq_zero_of_le (not_lt.1 hrm) h.nil
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at hxr'
    rw [E, Ideal.mem_comap, hxr']
    exact zero_mem _

theorem closed : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ (r : ℕ) (x : Lat.A f ξ l M),
    (∀ n : ℕ, x ∈ Ideal.span {(l : Lat.A f ξ l M) ^ n} ⊔ pdP (Lat.γ f ξ l M hc) r) →
    x ∈ pdP (Lat.γ f ξ l M hc) r := by
  intro W B _ _ _ f ξ l M m h hc r
  induction r with
  | zero =>
    intro x _
    rw [GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc 0]
    simp
  | succ r ih => exact closed_succ h hc r ih

end GlobalTheory.CompanionTheory.LatClosed

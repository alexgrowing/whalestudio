import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot

noncomputable section
open IsLocalRing UpperTheory.Et

private theorem one_add_mul_idem_pow {S : Type} [CommRing S] {e : S} (he : IsIdempotentElem e)
    (c : S) (n : ℕ) : (1 + c * e) ^ n = 1 + ((1 + c) ^ n - 1) * e := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : e * e = e := he
    rw [pow_succ, ih, pow_succ]
    linear_combination (((1 + c) ^ n - 1) * c) * h2

theorem UpperTheory.roots_of_unity_eq_locallyConstant_powers_spectrum :
    ∀ (S : Type) [CommRing S] (q : ℕ) [NeZero q] (ζ : S), GoodRoot q ζ →
      (∀ g : LocallyConstant (PrimeSpectrum S) (ZMod q), ∃ w : S, w ^ q = 1 ∧ ∀ p : PrimeSpectrum S, w - ζ ^ (g p).val ∈ p.asIdeal) ∧
      (∀ w : S, w ^ q = 1 → ∃ g : LocallyConstant (PrimeSpectrum S) (ZMod q), ∀ p : PrimeSpectrum S, w - ζ ^ (g p).val ∈ p.asIdeal) ∧
      ∀ (a b : ZMod q) (p : PrimeSpectrum S), ζ ^ a.val - ζ ^ b.val ∈ p.asIdeal → a = b := by
  intro S _ q _ ζ hζ
  obtain ⟨hq1, hunit, hsplit⟩ := hζ
  have notmem : ∀ (a b : ZMod q) (p : PrimeSpectrum S), a ≠ b →
      ζ ^ a.val - ζ ^ b.val ∉ p.asIdeal := by
    intro a b p hab hmem
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hunit a b hab))
  refine ⟨fun g => ?_, fun w hw => ?_, fun a b p h => ?_⟩
  · have hfib : ∀ a : ZMod q, ∃ e : S, IsIdempotentElem e ∧
        ∀ p : PrimeSpectrum S, (g p = a ↔ e ∉ p.asIdeal) := by
      intro a
      obtain ⟨e, he, hs⟩ := PrimeSpectrum.isClopen_iff.1 (g.isLocallyConstant.isClopen_fiber a)
      refine ⟨e, he, fun p => ?_⟩
      have := congrArg (p ∈ ·) hs
      simpa [PrimeSpectrum.mem_basicOpen] using this
    choose e he hge using hfib
    refine ⟨∏ a : ZMod q, (1 + (ζ ^ a.val - 1) * e a), ?_, fun p => ?_⟩
    · rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun a _ => ?_
      rw [one_add_mul_idem_pow (he a)]
      have hz : (1 + (ζ ^ a.val - 1)) ^ q = 1 := by
        rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hq1, one_pow]
      rw [hz, sub_self, zero_mul, add_zero]
    · have h0 : ∀ b, b ≠ g p → Ideal.Quotient.mk p.asIdeal (e b) = 0 := by
        intro b hb
        rw [Ideal.Quotient.eq_zero_iff_mem]
        by_contra h
        exact hb ((hge b p).2 h).symm
      have h1 : Ideal.Quotient.mk p.asIdeal (e (g p)) = 1 := by
        have hn : e (g p) ∉ p.asIdeal := (hge (g p) p).1 rfl
        have hm : e (g p) * (1 - e (g p)) ∈ p.asIdeal := by
          rw [mul_sub, mul_one, (he (g p)).eq, sub_self]
          exact p.asIdeal.zero_mem
        have h1m : 1 - e (g p) ∈ p.asIdeal := (p.isPrime.mem_or_mem hm).resolve_left hn
        rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk p.asIdeal), ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem]
        have := p.asIdeal.neg_mem h1m
        simpa using this
      rw [← Ideal.Quotient.eq, map_prod, Finset.prod_eq_single (g p)]
      · simp [h1]
      · intro b _ hb
        simp [h0 b hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
  · have hprod : ∏ a ∈ Finset.range q, (w - ζ ^ a) = 0 := by
      have := hsplit S (RingHom.id S) w
      simp only [RingHom.id_apply, hw, sub_self] at this
      exact this.symm
    have hex : ∀ p : PrimeSpectrum S, ∃ a : ZMod q, w - ζ ^ a.val ∈ p.asIdeal := by
      intro p
      have h0 : ∏ a ∈ Finset.range q, (w - ζ ^ a) ∈ p.asIdeal := by
        rw [hprod]
        exact p.asIdeal.zero_mem
      obtain ⟨a, ha, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (hp := p.isPrime)).1 h0
      refine ⟨(a : ZMod q), ?_⟩
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 ha)]
    choose g0 hg0 using hex
    have hiff : ∀ (p : PrimeSpectrum S) (a : ZMod q),
        g0 p = a ↔ ∀ b, b ≠ a → w - ζ ^ b.val ∉ p.asIdeal := by
      intro p a
      constructor
      · rintro rfl b hb hmem
        apply notmem b (g0 p) p hb
        have e1 : ζ ^ b.val - ζ ^ (g0 p).val = (w - ζ ^ (g0 p).val) - (w - ζ ^ b.val) := by ring
        rw [e1]
        exact p.asIdeal.sub_mem (hg0 p) hmem
      · intro h
        by_contra hne
        exact h (g0 p) hne (hg0 p)
    refine ⟨⟨g0, ?_⟩, hg0⟩
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    have hset : g0 ⁻¹' {a} = ⋂ b : ZMod q, ⋂ (_ : b ≠ a),
        (PrimeSpectrum.basicOpen (w - ζ ^ b.val) : Set (PrimeSpectrum S)) := by
      ext p
      simp [hiff, PrimeSpectrum.mem_basicOpen]
    rw [hset]
    exact isOpen_iInter_of_finite fun b => isOpen_iInter_of_finite fun _ =>
      (PrimeSpectrum.basicOpen _).isOpen
  · by_contra hab
    exact notmem a b p hab h

end

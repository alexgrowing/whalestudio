import Development.EtaleCohomology.EtaleSheaves.TorEtPf

noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf LateralTheory.E.TorEtPf

namespace LateralTheory.E.ProjFPf

section Tw
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

theorem twist_apply (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (k : ZMod q) :
    twist hε z k = ∑ c, ε c * z (k + c) := rfl

def tinv (ε : ZMod q → A) (z : ZMod q → A) : ZMod q → A := fun k => ∑ d, ε (-d) * z (k + d)

theorem twist_tinv (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : twist hε (tinv ε z) = z := by
  funext k
  rw [twist_apply]
  unfold tinv
  have : ∀ c, ε c * ∑ d, ε (-d) * z (k + c + d) = ε c * z k := by
    intro c
    rw [Finset.mul_sum, Finset.sum_eq_single (-c)]
    · rw [neg_neg, ← mul_assoc, (hε.idem c).eq, add_neg_cancel_right]
    · intro d _ hd
      have : c ≠ -d := fun h => hd (by rw [h, neg_neg])
      rw [← mul_assoc, hε.ortho this, zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul, hε.complete, one_mul]

theorem tinv_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : tinv ε (twist hε z) = z := by
  funext k
  unfold tinv
  simp_rw [twist_apply]
  have : ∀ d, ε (-d) * ∑ c, ε c * z (k + d + c) = ε (-d) * z k := by
    intro d
    rw [Finset.mul_sum, Finset.sum_eq_single (-d)]
    · rw [← mul_assoc, (hε.idem (-d)).eq, add_neg_cancel_right]
    · intro c _ hc
      rw [← mul_assoc, hε.ortho (Ne.symm hc), zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul]
  rw [show (∑ d : ZMod q, ε (-d)) = ∑ d, ε d from
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl), hε.complete, one_mul]

theorem twist_const_mul (hε : CompleteOrthogonalIdempotents ε) (a : A) (z : ZMod q → A) :
    twist hε (fun k => a * z k) = fun k => a * twist hε z k := by
  funext k
  simp only [twist_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem eq_zero_of_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (h : twist hε z = 0) : z = 0 := by
  rw [← tinv_twist hε z, h]; funext k; simp [tinv]
end Tw

section Main
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S)

theorem mem_tor {ε : ZMod q → Localization.Away (f * g)} (hε : CompleteOrthogonalIdempotents ε) (p : Amb f g q) :
    p ∈ Tor f g hε ↔ ∀ k, rL f g (p.1 k) = twist hε (fun j => rR f g (p.2 j)) k :=
  funext_iff

theorem rR_alg (a : S) : rR f g (algebraMap S (Localization.Away g) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rR; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem rL_alg (a : S) : rL f g (algebraMap S (Localization.Away f) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rL; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem unit_g : IsUnit (algebraMap S (Localization.Away (f * g)) g) := by
  refine isUnit_of_mul_isUnit_right (x := algebraMap S (Localization.Away (f * g)) f) ?_
  rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g)

theorem kill (z : Localization.Away g) (hz : rR f g z = 0) :
    ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * z = 0 := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
  dsimp only at hz ⊢
  have hb : algebraMap S (Localization.Away (f * g)) b = 0 := by
    rw [← rR_alg, ← IsLocalization.mk'_spec (Localization.Away g) b s, map_mul, hz, zero_mul]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ b).mp hb
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n)) :=
    (IsLocalization.map_units (Localization.Away g) s).mul
      (by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit g).pow n)
  refine (hu.mul_left_eq_zero).mp ?_
  calc algebraMap S (Localization.Away g) f ^ n * IsLocalization.mk' (Localization.Away g) b s *
        (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n))
      = algebraMap S (Localization.Away g) f ^ n *
        (IsLocalization.mk' (Localization.Away g) b s * algebraMap S (Localization.Away g) (s : S)) *
        algebraMap S (Localization.Away g) (g ^ n) := by ring
    _ = algebraMap S (Localization.Away g) ((f * g) ^ n * b) := by
        rw [IsLocalization.mk'_spec, mul_pow]; simp only [map_mul, map_pow]; ring
    _ = 0 := by simp only at hn; rw [hn, map_zero]
end Main

theorem projF : ProjF := by
  intro q _ S _ f g _ ε hε
  let _ := (torMap f g hε).toAlgebra
  let _ := (pr1 f g hε).toAlgebra
  have hA : ∀ t : Tor f g hε, algebraMap (Tor f g hε) (ZMod q → Localization.Away f) t = (t : Amb f g q).1 :=
    fun _ => rfl
  have hf : algebraMap S (Tor f g hε) f = torMap f g hε f := rfl
  have hT1 : ((torMap f g hε f : Tor f g hε) : Amb f g q).1 = fun _ => algebraMap S (Localization.Away f) f := rfl
  have hT2 : ((torMap f g hε f : Tor f g hε) : Amb f g q).2 = fun _ => algebraMap S (Localization.Away g) f := rfl
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [hA, hf, hT1, Pi.isUnit_iff]; intro _; exact IsLocalization.Away.algebraMap_isUnit f
  · intro s
    set w : ZMod q → Localization.Away (f * g) := tinv ε (fun k => rL f g (s k)) with hw
    obtain ⟨⟨_, n, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w
    have hb' : ∀ i, ∃ a, algebraMap S (Localization.Away (f * g)) a = (f * g) ^ n • w i :=
      fun i => RingHom.mem_rangeS.mp (hb i)
    choose a ha using hb'
    let y : ZMod q → Localization.Away g := fun k =>
      IsLocalization.mk' (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
    have hy : ∀ k, rR f g (y k) = algebraMap S _ (f ^ n) * w k := by
      intro k
      have hu : IsUnit (algebraMap S (Localization.Away (f * g)) (g ^ n)) := by
        rw [map_pow]; exact (unit_g f g).pow n
      apply hu.mul_left_injective
      have e1 := IsLocalization.mk'_spec (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
      simp only at e1 ⊢
      rw [← rR_alg f g (g ^ n), ← map_mul, e1]
      simp only [rR_alg, ha k, Algebra.smul_def, mul_pow, map_mul, map_pow]
      ring
    let x : ZMod q → Localization.Away f := fun k => s k * algebraMap S _ f ^ n
    have hmem : ((x, y) : Amb f g q) ∈ Tor f g hε := by
      rw [mem_tor]; intro k
      have h2 : (fun j => rR f g (((x, y) : Amb f g q).2 j)) = fun j => algebraMap S _ (f ^ n) * w j := funext hy
      rw [h2, twist_const_mul, hw, twist_tinv]
      show rL f g (s k * algebraMap S _ f ^ n) = _
      rw [map_mul, map_pow, rL_alg, map_pow]; ring
    refine ⟨n, ⟨(x, y), hmem⟩, ?_⟩
    show s * (((torMap f g hε f : Tor f g hε) : Amb f g q).1) ^ n = x
    rw [hT1]
    funext k
    simp only [Pi.mul_apply, Pi.pow_apply]
    rfl
  · intro a b hab
    have hc1 : ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by
      rw [← hA (a - b), map_sub, hab, sub_self]
    have hm := (mem_tor f g hε _).mp (a - b).2
    have htw : twist hε (fun j => rR f g (((a - b : Tor f g hε) : Amb f g q).2 j)) = 0 := by
      funext k; rw [← hm k, hc1]; simp
    have hc2 := eq_zero_of_twist hε _ htw
    have hk : ∀ k, ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * ((a - b : Tor f g hε) : Amb f g q).2 k = 0 :=
      fun k => kill f g _ (congrFun hc2 k)
    choose m hm' using hk
    refine ⟨Finset.univ.sup m, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    apply Subtype.ext
    apply Prod.ext
    · have e : ((algebraMap S (Tor f g hε) f ^ Finset.univ.sup m : Tor f g hε) : Amb f g q).1 *
          ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by rw [hc1, mul_zero]
      exact e
    · funext k
      show (algebraMap S (Localization.Away g) f) ^ (Finset.univ.sup m) * ((a - b : Tor f g hε) : Amb f g q).2 k = 0
      rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : m k ≤ Finset.univ.sup m), pow_add, mul_assoc, hm' k,
        mul_zero]

end LateralTheory.E.ProjFPf

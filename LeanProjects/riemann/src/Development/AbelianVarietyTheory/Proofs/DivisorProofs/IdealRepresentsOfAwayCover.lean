import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsKillIdeal

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem exists_pow_mul_eq_zero_of_represents_away {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop}
    (hbc : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
      Q R' f → Q R'' (g.comp f))
    (a : A) {Ja : Ideal (Localization.Away a)}
    (hJa : Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) Ja)
    {R' : Type} [CommRing R'] (f : A →+* R') (hf : Q R' f) (x : A)
    (hx : algebraMap A (Localization.Away a) x ∈ Ja) : ∃ m : ℕ, f a ^ m * f x = 0 := by
  have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
      (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
  have h1 : Q _ ((algebraMap R' (Localization.Away (f a))).comp f) :=
    hbc _ _ (algebraMap R' (Localization.Away (f a))) f hf
  rw [← e] at h1
  have h2 := (hJa _ (Localization.awayMap f a)).1 h1 hx
  rw [RingHom.mem_ker, ← RingHom.comp_apply, e, RingHom.comp_apply,
    IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))] at h2
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := h2
  exact ⟨m, hm⟩

theorem represents_of_away_cover : ∀ (A : Type) [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
    Q R' f → Q R'' (g.comp f)) →
  (∀ (R' : Type) [CommRing R'] (f : A →+* R') (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
    (∀ r ∈ t, Q (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) → Q R' f) →
  ∀ (s : Finset A), Ideal.span (s : Set A) = ⊤ →
  (∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
    Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) J) →
  ∃ J : Ideal A, Represents Q J := by
  classical
  intro A _ Q hbc hloc s hs hJ
  choose! J' hJ' using hJ
  refine ⟨⨅ a ∈ s, (J' a).comap (algebraMap A (Localization.Away a)),
    fun R' _ f ↦ ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩⟩
  · intro x hx
    simp only [Submodule.mem_iInf, Ideal.mem_comap] at hx
    rw [RingHom.mem_ker]
    have hspan : Ideal.span ((f : A → R') '' (s : Set A)) = ⊤ := by
      rw [← Ideal.map_span, hs, Ideal.map_top]
    have := Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule R' R') _ hspan (f x) ?_
    · simpa using this
    rintro ⟨_, b, hb, rfl⟩
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc b (hJ' b hb) f hf x (hx b hb)
    exact ⟨m, by simpa [smul_eq_mul] using hm⟩
  · apply hloc R' f (s.image f)
    · rw [Finset.coe_image, ← Ideal.map_span, hs, Ideal.map_top]
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hr
    have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
        (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
    rw [← e]
    refine ((hJ' a ha) _ (Localization.awayMap f a)).2 ?_
    intro j hj
    obtain ⟨⟨y, _, n, rfl⟩, hy⟩ := IsLocalization.surj (Submonoid.powers a) j
    simp only at hy
    have hyJ : algebraMap A (Localization.Away a) y ∈ J' a := hy ▸ Ideal.mul_mem_right _ _ hj
    have hb : ∀ b ∈ s, ∃ m : ℕ, algebraMap A (Localization.Away b) (a ^ m * y) ∈ J' b := by
      intro b hbs
      let p : A →+* (Localization.Away b ⧸ J' b) :=
        (Ideal.Quotient.mk (J' b)).comp (algebraMap A (Localization.Away b))
      have hp : Q _ p := ((hJ' b hbs) _ (Ideal.Quotient.mk (J' b))).2 (by rw [Ideal.mk_ker])
      obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc a (hJ' a ha) p hp y hyJ
      refine ⟨m, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [p] using hm
    choose! m hm using hb
    have hM : a ^ (s.sup m) * y ∈ ⨅ b ∈ s, (J' b).comap (algebraMap A (Localization.Away b)) := by
      simp only [Submodule.mem_iInf, Ideal.mem_comap]
      intro b hbs
      have : a ^ (s.sup m) * y = a ^ (s.sup m - m b) * (a ^ m b * y) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hbs)]
      rw [this, map_mul]
      exact Ideal.mul_mem_left _ _ (hm b hbs)
    have h0 := hf hM
    rw [RingHom.mem_ker, map_mul, map_pow] at h0
    rw [RingHom.mem_ker]
    have hu : IsUnit (Localization.awayMap f a (algebraMap A _ (a ^ n))) := by
      rw [← RingHom.comp_apply, e, RingHom.comp_apply, map_pow]
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f a)) (f a)).pow n
    have h3 : Localization.awayMap f a j * Localization.awayMap f a (algebraMap A _ (a ^ n)) = 0 := by
      rw [← map_mul, hy, ← RingHom.comp_apply, e, RingHom.comp_apply,
        IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))]
      exact ⟨⟨_, s.sup m, rfl⟩, h0⟩
    exact (hu.mul_left_eq_zero).1 h3

end GlobalTheory.PtClosed

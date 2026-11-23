import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

private theorem under_le_one {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (ι : K →+* L)
    (w : HeightOneSpectrum (𝓞 L)) : ∃ v : HeightOneSpectrum (𝓞 K),
    (∀ x : K, v.valuation K x ≤ 1 ↔ w.valuation L (ι x) ≤ 1) ∧
    (∀ x : K, v.valuation K x < 1 ↔ w.valuation L (ι x) < 1) := by
  letI : Algebra K L := ι.toAlgebra
  have he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot
  refine ⟨w.under (𝓞 K), fun x => ?_, fun x => ?_⟩
  · have h := HeightOneSpectrum.valuation_liesOver L (w.under (𝓞 K)) w x
    change _ ↔ w.valuation L (algebraMap K L x) ≤ 1
    rw [← h, pow_le_one_iff he]
  · have h := HeightOneSpectrum.valuation_liesOver L (w.under (𝓞 K)) w x
    change _ ↔ w.valuation L (algebraMap K L x) < 1
    rw [← h, pow_lt_one_iff he]

private theorem val_nonneg_iff (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp
  · have h0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    rw [D.val_eq w x hx, ← WithTop.coe_zero, WithTop.coe_le_coe, vAdd, neg_nonneg,
      WithZero.log_le_iff_le_exp h0, WithZero.exp_zero]

private theorem val_resChar_lt (D : D7) (w : D.what₂.places.Pl) :
    (D.plEq w).valuation D.what₂.LL (D.what₂.places.resChar w : D.what₂.LL) < 1 := by
  have hx : (D.what₂.places.resChar w : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have h0 : (D.plEq w).valuation D.what₂.LL (D.what₂.places.resChar w : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hx
  have h := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hx, WithTop.coe_inj, vAdd] at h
  have hp := D.what₂.places.ramIdx_pos w
  rw [← WithZero.exp_zero, ← WithZero.log_lt_iff_lt_exp h0]
  omega

private theorem prime_eq_of_lt {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (h1 : w.valuation L (p : L) < 1) (h2 : w.valuation L (q : L) < 1) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : 𝓞 L) (q : 𝓞 L) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  have a1 : (p : 𝓞 L) ∈ w.asIdeal := (w.valuation_lt_one_iff_mem (K := L) _).1 (by simpa using h1)
  have a2 : (q : 𝓞 L) ∈ w.asIdeal := (w.valuation_lt_one_iff_mem (K := L) _).1 (by simpa using h2)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ a1) (w.asIdeal.mul_mem_left _ a2)))

private theorem exists_under {D D' : D7} (ι : D.what₂.LL →+* D'.what₂.LL) (w' : D'.what₂.places.Pl) :
    ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = D'.what₂.places.resChar w' ∧
      ∀ x, 0 ≤ D.what₂.places.val w x ↔ 0 ≤ D'.what₂.places.val w' (ι x) := by
  obtain ⟨v, h1, h2⟩ := under_le_one ι (D'.plEq w')
  obtain ⟨w, rfl⟩ := D.plEq.surjective v
  refine ⟨w, ?_, fun x => ?_⟩
  · have a := (h2 _).1 (val_resChar_lt D w)
    rw [map_natCast] at a
    exact prime_eq_of_lt _ (D.what₂.places.resChar_prime w) (D'.what₂.places.resChar_prime w') a (val_resChar_lt D' w')
  · rw [val_nonneg_iff, val_nonneg_iff, h1]

theorem UpperTheory.sidePlace_exists_of_copyAll :
    ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → (∀ w : D.what₂.places.Pl, ∃ i, D.ntw.l i = D.what₂.places.resChar w ∧ GlobalTheory.HeightCounting.SidePl D w i true) → ∀ w : D'.what₂.places.Pl, ∃ i, D'.ntw.l i = D'.what₂.places.resChar w ∧ GlobalTheory.HeightCounting.SidePl D' w i true := by
  intro D D' ι e h H w'
  obtain ⟨w, hr, hv⟩ := exists_under ι w'
  obtain ⟨i, hl, hs⟩ := H w
  have hL := h.cp.LL0
  have hE := h.cp.emb0
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  refine ⟨i, hl.trans hr, fun x => ?_⟩
  have a := hs (e x)
  rw [hv, hL x] at a
  have b : D.ntw.emb0 i (e x) = (overD D r).ntw.emb0 i x := eq_of_heq (hE i i HEq.rfl x)
  rw [if_pos rfl, b] at a
  rw [if_pos rfl]
  exact a

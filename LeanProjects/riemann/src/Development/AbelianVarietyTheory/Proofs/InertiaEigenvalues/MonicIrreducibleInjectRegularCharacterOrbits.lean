import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.PrimeLabOrbit

variable {g : ℕ} [hg : Fact g.Prime]

theorem aeval_pow_frob {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) (Q : (ZMod g)[X]) (y : K) :
    aeval (y ^ g ^ n) Q = (aeval y Q) ^ g ^ n := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  rw [← iterateFrobenius_def g n y, ← iterateFrobenius_def g n (aeval y Q), aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

theorem frob_injective {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) :
    Function.Injective (fun y : K => y ^ g ^ n) := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  intro a b h
  apply (iterateFrobenius K g n).injective
  simpa only [iterateFrobenius_def] using h

theorem card_le_of_gen_fixed {L : Type} [Field L] [Algebra (ZMod g) L] [Fintype L] {k : ℕ} (hk : 0 < k) {x : L}
    (hgen : ∀ y : L, ∃ Q : (ZMod g)[X], aeval x Q = y) (hx : x ^ g ^ k = x) : Fintype.card L ≤ g ^ k := by
  have hq : 1 < g ^ k := Nat.one_lt_pow hk.ne' hg.out.one_lt
  set f : L[X] := X ^ (g ^ k) - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L hq
  have hfix : ∀ y : L, y ^ g ^ k = y := by
    intro y
    obtain ⟨Q, rfl⟩ := hgen y
    rw [← aeval_pow_frob, hx]
  have hsub : (Finset.univ : Finset L) ⊆ f.roots.toFinset := by
    intro y _
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hf, eval_sub, eval_pow, eval_X, hfix y, sub_self]
  calc Fintype.card L = (Finset.univ : Finset L).card := Finset.card_univ.symm
    _ ≤ f.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := card_roots' f
    _ = g ^ k := FiniteField.X_pow_card_sub_X_natDegree_eq L hq

section adjoin

variable {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P)
include hP

theorem finrank_adjoin : haveI := Fact.mk hP.2.1; Module.finrank (ZMod g) (AdjoinRoot P) = d := by
  haveI := Fact.mk hP.2.1
  rw [(AdjoinRoot.powerBasis hP.1.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hP.2.2.2]

theorem adjoin_gen : ∀ y : AdjoinRoot P, ∃ Q : (ZMod g)[X], aeval (AdjoinRoot.root P) Q = y := by
  intro y
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective y
  exact ⟨Q, AdjoinRoot.aeval_eq Q⟩

theorem le_of_dvd {k : ℕ} (hk : 0 < k) (hdvd : P ∣ X ^ (g ^ k) - X) : d ≤ k := by
  haveI := Fact.mk hP.2.1
  haveI : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.1.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot P) = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, finrank_adjoin hP]
  have hx : (AdjoinRoot.root P) ^ g ^ k = AdjoinRoot.root P := by
    obtain ⟨R, hR⟩ := hdvd
    have h0 : aeval (AdjoinRoot.root P) (X ^ (g ^ k) - X : (ZMod g)[X]) = 0 := by
      rw [hR, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
    rw [map_sub, map_pow, aeval_X, sub_eq_zero] at h0
    exact h0
  have := card_le_of_gen_fixed (L := AdjoinRoot P) (x := AdjoinRoot.root P) hk (adjoin_gen hP) hx
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right hg.out.one_lt).1 this

end adjoin

variable {K : Type} [Field K] [Algebra (ZMod g) K]

theorem exists_unit_root {d : ℕ} (hd : 0 < d) (hK : Module.finrank (ZMod g) K = d) {P : (ZMod g)[X]}
    (hP : IsPrimeLab d P) : ∃ u : Kˣ, aeval (u : K) P = 0 := by
  haveI := Fact.mk hP.2.1
  haveI : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.1.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite _
  have hc : Fintype.card (AdjoinRoot P) = Fintype.card K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), Module.card_eq_pow_finrank (K := ZMod g) (V := K),
      finrank_adjoin hP, hK]
  let φ := FiniteField.algEquivOfCardEq g hc
  have hr : aeval (φ (AdjoinRoot.root P)) P = 0 := by
    rw [show φ (AdjoinRoot.root P) = φ.toAlgHom (AdjoinRoot.root P) from rfl, aeval_algHom_apply,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hne : φ (AdjoinRoot.root P) ≠ 0 := by
    intro h0
    rw [h0, aeval_def, eval₂_at_zero] at hr
    exact hP.2.2.1 ((algebraMap (ZMod g) K).injective (hr.trans (map_zero _).symm))
  exact ⟨Units.mk0 _ hne, hr⟩

theorem orbit_regular {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P) {u : K} (hu : aeval u P = 0) :
    ∀ i j, i < d → j < d → u ^ g ^ i = u ^ g ^ j → i = j := by
  have key : ∀ i j, i < j → j < d → u ^ g ^ i = u ^ g ^ j → False := by
    intro i j hij hj h
    have hk : 0 < j - i := Nat.sub_pos_of_lt hij
    have hfix : u ^ g ^ (j - i) = u := by
      apply frob_injective (g := g) (K := K) i
      simp only
      rw [h, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
    have hmin : P = minpoly (ZMod g) u := minpoly.eq_of_irreducible_of_monic hP.2.1 hu hP.1
    have hdvd : P ∣ X ^ (g ^ (j - i)) - X := by
      rw [hmin]
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, hfix, sub_self]
    have := le_of_dvd hP hk hdvd
    omega
  intro i j hi hj h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij hj h).elim
  · exact hij
  · exact (key j i hij hi h.symm).elim

theorem primeLab_to_regularChar : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d → ∃ c : (ZMod g)[X] → (Kˣ →* ℂˣ), (∀ P, IsPrimeLab d P → IsRegularChar g d (c P)) ∧
      ∀ P P', IsPrimeLab d P → IsPrimeLab d P' → (∃ i < d, c P' = c P ^ g ^ i) → P = P' := by
  intro g _ d hd K _ _ hK
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  let e : Kˣ ≃* (Kˣ →* ℂˣ) := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Kˣ ℂ).some.symm
  let c : (ZMod g)[X] → (Kˣ →* ℂˣ) := fun P =>
    if h : ∃ u : Kˣ, aeval (u : K) P = 0 then e h.choose else 1
  have hc : ∀ P, IsPrimeLab d P → ∃ u : Kˣ, aeval (u : K) P = 0 ∧ c P = e u := by
    intro P hP
    have h := exists_unit_root hd hK hP
    exact ⟨h.choose, h.choose_spec, dif_pos h⟩
  refine ⟨c, fun P hP => ?_, fun P P' hP hP' ⟨i, hi, h⟩ => ?_⟩
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    intro i j hi hj h
    rw [hcu, ← map_pow, ← map_pow] at h
    have h' := congrArg Units.val (e.injective h)
    simp only [Units.val_pow_eq_pow_val] at h'
    exact orbit_regular hP hu i j hi hj h'
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    obtain ⟨u', hu', hcu'⟩ := hc P' hP'
    rw [hcu, hcu', ← map_pow] at h
    have h' := congrArg Units.val (e.injective h)
    simp only [Units.val_pow_eq_pow_val] at h'
    have hr : aeval (u' : K) P = 0 := by rw [h', aeval_pow_frob, hu, zero_pow (pow_ne_zero _ (Fact.out : g.Prime).ne_zero)]
    rw [minpoly.eq_of_irreducible_of_monic hP.2.1 hr hP.1, minpoly.eq_of_irreducible_of_monic hP'.2.1 hu' hP'.1]

end GlobalTheory.PrimeLabOrbit

end

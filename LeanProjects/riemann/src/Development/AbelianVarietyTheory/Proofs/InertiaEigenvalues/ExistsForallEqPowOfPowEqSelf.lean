import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusPowerEmbeddings

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues.FrobPow

open Polynomial

theorem eq_of_pow_eq_self_of_map_eq {O k : Type} [CommRing O] [IsDomain O] [Field k]
    (φ : O →+* k) (q : ℕ) (hq : (q : k) = 0) {y z : O} (hy : y ^ q = y) (hz : z ^ q = z)
    (h : φ y = φ z) : y = z := by
  have h1 := Commute.geom_sum₂_mul (Commute.all y z) q
  rw [hy, hz] at h1
  have h2 : ((∑ i ∈ Finset.range q, y ^ i * z ^ (q - 1 - i)) - 1) * (y - z) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    have h4 := congrArg φ h3
    simp only [map_sub, map_sum, map_mul, map_pow, map_one, map_zero, h] at h4
    rw [geom_sum₂_self, hq, zero_mul, zero_sub, neg_eq_zero] at h4
    exact one_ne_zero h4
  · exact sub_eq_zero.1 h3

theorem exists_forall_eq_pow_of_pow_eq_self (l : ℕ) [Fact l.Prime] {O k : Type} [CommRing O]
    [IsDomain O] [Field k] [CharP k l] (φ : O →+* k) (τ : O →+* O)
    (hτ : ∀ x, φ x = 0 → φ (τ x) = 0) (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ, ∀ x : O, x ^ l ^ n = x → τ x = x ^ l ^ a := by
  classical
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let S : Set O := {x | x ^ l ^ n = x}
  have hmon : ∀ (A : Type) [CommRing A] [Nontrivial A], (X ^ l ^ n - X : A[X]).Monic := by
    intro A _ _
    apply Monic.sub_of_left (monic_X_pow _)
    rw [degree_X, degree_X_pow]
    exact_mod_cast hq
  have hS : S.Finite := by
    refine (X ^ l ^ n - X : O[X]).roots.toFinset.finite_toSet.subset fun x hx => ?_
    have hx' : x ^ l ^ n = x := hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [mem_roots (hmon O).ne_zero]
    simp [hx']
  have hint : ∀ x ∈ S, IsIntegral ℤ x := by
    intro x hx
    have hx' : x ^ l ^ n = x := hx
    exact ⟨X ^ l ^ n - X, hmon ℤ, by simp [hx']⟩
  have hfin : Module.Finite ℤ (Algebra.adjoin ℤ S) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hS hint
  let ι : Algebra.adjoin ℤ S →+* O := (Algebra.adjoin ℤ S).val.toRingHom
  obtain ⟨a, ha⟩ := GlobalTheory.exists_forall_eq_pow_of_ker_le l (Algebra.adjoin ℤ S) k (φ.comp ι)
    (φ.comp (τ.comp ι)) (fun x hx => hτ _ hx)
  refine ⟨a, fun x hx => ?_⟩
  have h1 : φ (τ x) = φ x ^ l ^ a := ha ⟨x, Algebra.subset_adjoin hx⟩
  refine eq_of_pow_eq_self_of_map_eq φ (l ^ n) ?_ ?_ ?_ ?_
  · rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn.ne']
  · rw [← map_pow, hx]
  · rw [← pow_mul, mul_comm, pow_mul, hx]
  · rw [h1, map_pow]

theorem exists_gal_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) (σ : GQ l) :
    ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a := by
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let v : Valuation (Om l) NNReal := (PadicAlgCl.valued l).v
  have hv : ∀ x : Om l, v (σ x) = v x := fun x =>
    NNReal.eq (spectralNorm_eq_of_equiv σ x).symm
  let O : ValuationSubring (Om l) := v.valuationSubring
  have hO : ∀ x : Om l, x ∈ O ↔ v x ≤ 1 := fun x => Iff.rfl
  have hm : ∀ x : O, IsLocalRing.residue O x = 0 ↔ v x < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff _ v
  have hch : CharP (IsLocalRing.ResidueField O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl).2 ?_
    rw [← map_natCast (IsLocalRing.residue O), hm]
    have : v (l : Om l) = 1 / (l : NNReal) := PadicAlgCl.valuation_p l
    rw [SubringClass.coe_natCast, this, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  let τ : O →+* O := (σ : Om l →+* Om l).restrict O O (fun x hx => by
    rw [hO] at hx ⊢
    exact (hv x).trans_le hx)
  have hτ : ∀ x : O, ((τ x : O) : Om l) = σ x := fun x => rfl
  obtain ⟨a, ha⟩ := exists_forall_eq_pow_of_pow_eq_self l (IsLocalRing.residue O) τ
    (fun x hx => by rw [hm] at hx ⊢; rw [hτ, hv]; exact hx) n hn
  refine ⟨a, fun x hx => ?_⟩
  have hxO : x ∈ O := by
    rw [hO]
    by_contra h
    have h' : 1 < v x := not_le.1 h
    have h2 : v x ^ 1 < v x ^ l ^ n := pow_lt_pow_right₀ h' hq
    rw [← map_pow, ← map_pow, hx, pow_one] at h2
    exact lt_irrefl _ h2
  have h3 := ha ⟨x, hxO⟩ (Subtype.ext (by simpa using hx))
  have h4 := congrArg (fun y : O => (y : Om l)) h3
  simpa [hτ] using h4

end GlobalTheory.InertiaEigenvalues.FrobPow

import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzKOrb

open Polynomial GlobalTheory.GLq GlobalTheory.Published
open scoped IntermediateField

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

theorem exists_elliptic [FiniteDimensional (ZMod g) K] (hfr : Module.finrank (ZMod g) K = n) (z : Kˣ)
    (hz : (minpoly (ZMod g) (z : K)).natDegree = n) :
    ∃ y : Gn g n, Irreducible (y : Mt g n).charpoly ∧ aeval (z : K) (y : Mt g n).charpoly = 0 := by
  let b : Module.Basis (Fin n) (ZMod g) K := Module.finBasisOfFinrankEq (ZMod g) K hfr
  let L := Algebra.leftMulMatrix b
  refine ⟨Units.map (L : K →* Matrix (Fin n) (Fin n) (ZMod g)) z, ?_⟩
  have hy : ((Units.map (L : K →* Matrix (Fin n) (Fin n) (ZMod g)) z : Gn g n) : Mt g n) = L (z : K) := rfl
  rw [hy]
  have hc : aeval (z : K) (L (z : K)).charpoly = 0 := by
    have h1 := Matrix.aeval_self_charpoly (L (z : K))
    rw [aeval_algHom_apply] at h1
    exact Algebra.leftMulMatrix_injective b (h1.trans (map_zero L).symm)
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  have hdvd := minpoly.dvd (ZMod g) (z : K) hc
  have heq : (L (z : K)).charpoly = minpoly (ZMod g) (z : K) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (Matrix.charpoly_monic _) hdvd
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hz])
  rw [heq]
  exact ⟨minpoly.irreducible hint, minpoly.aeval _ _⟩

theorem bad_of_deg [FiniteDimensional (ZMod g) K] (hn : 0 < n) (hfr : Module.finrank (ZMod g) K = n) (z : Kˣ)
    (hz : (minpoly (ZMod g) (z : K)).natDegree ≠ n) : ∃ i ∈ Finset.Icc 1 (n / 2), z ^ g ^ i = z := by
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  set d := (minpoly (ZMod g) (z : K)).natDegree with hd
  have hd1 : 0 < d := minpoly.natDegree_pos hint
  have hfd : Module.finrank (ZMod g) (ZMod g)⟮(z : K)⟯ = d := IntermediateField.adjoin.finrank hint
  have htow := Module.finrank_mul_finrank (ZMod g) (ZMod g)⟮(z : K)⟯ K
  rw [hfd, hfr] at htow
  set r := Module.finrank (ZMod g)⟮(z : K)⟯ K
  have hr1 : r ≠ 1 := by
    intro h1; rw [h1, mul_one] at htow; exact hz htow
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, mul_zero] at htow; omega
  have h2d : d * 2 ≤ n := by
    rw [← htow]; exact Nat.mul_le_mul_left _ (by omega)
  refine ⟨d, Finset.mem_Icc.2 ⟨hd1, (Nat.le_div_iff_mul_le (by norm_num)).2 h2d⟩, ?_⟩
  have : Finite K := Module.finite_of_finite (ZMod g)
  have : Finite (ZMod g)⟮(z : K)⟯ := Finite.of_injective _ Subtype.val_injective
  letI : Fintype (ZMod g)⟮(z : K)⟯ := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod g)⟮(z : K)⟯ = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hfd]
  have hx := FiniteField.pow_card (⟨(z : K), IntermediateField.mem_adjoin_simple_self _ _⟩ : (ZMod g)⟮(z : K)⟯)
  rw [hcard] at hx
  have hx' := congrArg Subtype.val hx
  simp only [IntermediateField.coe_pow] at hx'
  exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hx')

theorem card_fixed_le [Fintype K] [DecidableEq K] (i : ℕ) (hi : 0 < i) :
    (Finset.univ.filter fun z : Kˣ => z ^ g ^ i = z).card ≤ g ^ i := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hq : 1 < g ^ i := Nat.one_lt_pow hi.ne' hg
  have hne := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  calc (Finset.univ.filter fun z : Kˣ => z ^ g ^ i = z).card
      ≤ ((X ^ g ^ i - X : K[X]).roots.toFinset).card := by
        refine Finset.card_le_card_of_injOn (fun z : Kˣ => (z : K)) ?_ ?_
        · intro z hz
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz
          simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X]
          rw [← Units.val_pow_eq_pow_val, hz, sub_self]
        · intro x _ y _ h; exact Units.ext h
    _ ≤ (X ^ g ^ i - X : K[X]).roots.card := Multiset.toFinset_card_le _
    _ ≤ (X ^ g ^ i - X : K[X]).natDegree := card_roots' _
    _ = g ^ i := hdeg

end DiscreteGroups.sglob.DzType.Kon

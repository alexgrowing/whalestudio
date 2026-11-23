import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.MassEqZeroOfNotPrimary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

open Polynomial GlobalTheory.CuspGL GlobalTheory.GLq
open scoped IntermediateField

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

theorem trace_eq_nextCoeff {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (y : Mt g n) :
    Matrix.trace y = -(LinearMap.charpoly (Matrix.toLin' y)).nextCoeff := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Matrix.charpoly_toLin', Matrix.trace_eq_neg_charpoly_coeff, nextCoeff_of_natDegree_pos,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hn

theorem trace_eq_hT {g n : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    [FiniteDimensional (ZMod g) K] (hfr : Module.finrank (ZMod g) K = n)
    (ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g)) (ψ : ZMod g → ℂ) (z : K) :
    hT n ψ (ι z) = ψ (Algebra.trace (ZMod g) K z) := by
  unfold hT
  rw [minpoly.algHom_eq ι ι.injective z, trace_eq_finrank_mul_minpoly_nextCoeff]
  have hint : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  have hfd : Module.finrank (ZMod g) (ZMod g)⟮z⟯ = (minpoly (ZMod g) z).natDegree :=
    IntermediateField.adjoin.finrank hint
  have htow := Module.finrank_mul_finrank (ZMod g) (ZMod g)⟮z⟯ K
  rw [hfd, hfr] at htow
  have hd1 : 0 < (minpoly (ZMod g) z).natDegree := minpoly.natDegree_pos hint
  have hr : n / (minpoly (ZMod g) z).natDegree = Module.finrank (ZMod g)⟮z⟯ K := by
    rw [← htow, Nat.mul_div_cancel_left _ hd1]
  rw [hr, (minpoly.monic hint).nextCoeff_pow, nsmul_eq_mul]
  congr 1
  ring

theorem aC_eq_gs {g n : ℕ} [Fact g.Prime] (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Nat.card K = g ^ n) (θ₀ : AlgebraicClosure (ZMod g) →* ℂ)
    (ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g)) (θ : Kˣ →* ℂˣ) (k : ℕ)
    (hlink : ∀ u : Kˣ, ((θ u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) ^ k) (ψ₀ : AddChar (ZMod g) Circle) :
    aC n θ₀ (hT n fun a => ((ψ₀ a : Circle) : ℂ)) k =
      ((g ^ n - 1 : ℕ) : ℂ)⁻¹ * ∑ᶠ z : Kˣ, ((θ⁻¹ z : ℂˣ) : ℂ) * ((ψ₀ (Algebra.trace (ZMod g) K (z : K)) : Circle) : ℂ) := by
  classical
  have hgp : g.Prime := Fact.out
  have hKpos : 0 < Nat.card K := by rw [hK]; exact pow_pos hgp.pos _
  have : Finite K := Nat.finite_of_card_ne_zero hKpos.ne'
  let _ : Fintype K := Fintype.ofFinite K
  have : FiniteDimensional (ZMod g) K := Module.Finite.of_finite
  have hcard : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hcard] at h1
    exact (Nat.pow_right_injective hgp.two_le h1).symm
  have hq : Nat.card (ZMod g) = g := Nat.card_zmod g
  have hU : Fintype.card Kˣ = g ^ n - 1 := by rw [Fintype.card_units, hcard]
  unfold aC
  rw [hq]
  congr 1
  have hN : 0 < g ^ n - 1 := by
    have := Nat.one_lt_pow hn.ne' hgp.one_lt; omega
  have htor : tor (ZMod g) n = {α | α ^ (g ^ n - 1) = 1} := by unfold tor; rw [hq]
  have hmaps : Set.MapsTo (fun z : Kˣ => ι (z : K)) Set.univ (tor (ZMod g) n) := by
    intro z _
    rw [htor]
    show ι (z : K) ^ (g ^ n - 1) = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hU, pow_card_eq_one, Units.val_one, map_one]
  have hinj : Set.InjOn (fun z : Kˣ => ι (z : K)) Set.univ :=
    fun x _ y _ h => Units.ext (ι.injective h)
  have hfinT : (tor (ZMod g) n).Finite := by
    rw [htor]
    refine (Polynomial.nthRoots (g ^ n - 1) (1 : AlgebraicClosure (ZMod g))).finite_toSet.subset ?_
    intro α hα
    exact (Polynomial.mem_nthRoots hN).2 hα
  have hsurj : Set.SurjOn (fun z : Kˣ => ι (z : K)) Set.univ (tor (ZMod g) n) := by
    have hsub : (fun z : Kˣ => ι (z : K)) '' Set.univ ⊆ tor (ZMod g) n := hmaps.image_subset
    have hle : (tor (ZMod g) n).ncard ≤ ((fun z : Kˣ => ι (z : K)) '' Set.univ).ncard := by
      have hinj' : Function.Injective (fun z : Kˣ => ι (z : K)) := fun x y h => Units.ext (ι.injective h)
      rw [Set.ncard_image_of_injective _ hinj', Set.ncard_univ,
        Nat.card_eq_fintype_card, hU]
      calc (tor (ZMod g) n).ncard
          ≤ ((Polynomial.nthRoots (g ^ n - 1) (1 : AlgebraicClosure (ZMod g))).toFinset : Set _).ncard := by
            refine Set.ncard_le_ncard (t := ((Polynomial.nthRoots (g ^ n - 1)
              (1 : AlgebraicClosure (ZMod g))).toFinset : Set (AlgebraicClosure (ZMod g)))) ?_ (Finset.finite_toSet _)
            intro α hα
            rw [htor] at hα
            exact Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots hN).2 hα)
        _ = (Polynomial.nthRoots (g ^ n - 1) (1 : AlgebraicClosure (ZMod g))).toFinset.card :=
            Set.ncard_coe_finset _
        _ ≤ (Polynomial.nthRoots (g ^ n - 1) (1 : AlgebraicClosure (ZMod g))).card := Multiset.toFinset_card_le _
        _ ≤ g ^ n - 1 := Polynomial.card_nthRoots _ _
    have heq := Set.eq_of_subset_of_ncard_le hsub hle hfinT
    rw [← heq]
    exact Set.surjOn_image _ _
  have hbij : Set.BijOn (fun z : Kˣ => ι (z : K)) Set.univ (tor (ZMod g) n) := ⟨hmaps, hinj, hsurj⟩
  rw [← finsum_mem_univ (fun z : Kˣ => ((θ⁻¹ z : ℂˣ) : ℂ) * ((ψ₀ (Algebra.trace (ZMod g) K (z : K)) : Circle) : ℂ))]
  symm
  refine finsum_mem_eq_of_bijOn (fun z : Kˣ => ι (z : K)) hbij fun z _ => ?_
  rw [trace_eq_hT hfr ι, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hlink z, mul_comm]
  congr 1
  have hpow : (θ₀ (ι (z : K)) ^ k) ^ (g ^ n - 1) = 1 := by
    rw [← hlink z, ← Units.val_pow_eq_pow_val, ← map_pow, ← hU, pow_card_eq_one, map_one, Units.val_one]
  exact (star_eq_inv_of_pow hN hpow).symm

end DiscreteGroups.sglob.DzType.Kon

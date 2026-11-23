import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqProdOfMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulPolyNorm

open Polynomial GlobalTheory.PolyNorm

theorem eq_prod_aroots : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (d : ℕ) (δ : Polynomial ℤ → ℚ) (P : Polynomial ℚ), (∀ F G, δ (F * G) = δ F * δ G) → (∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * d) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i)) → P.Monic → P.natDegree = 2 * d → (∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X)) → ∀ F : Polynomial ℤ, algebraMap ℚ Ω (δ F) = ((P.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  intro Ω _ _ _ d δ P hm hΦ0 hP hPd hPe
  choose Φ hh hΦ using fun r : ℕ => hΦ0 r (fun i : Fin r => (X : ℤ[X]) ^ (i : ℕ))
  have hN : ∀ r (F : ℤ[X]), F.natDegree < r → δ F = ev (Φ r) (F.map (Int.castRingHom ℚ)) := by
    intro r F hF
    have := hΦ r fun i => F.coeff i
    have e : ∑ i : Fin r, F.coeff i • (X : ℤ[X]) ^ (i : ℕ) = F := by
      conv_rhs => rw [← gen_coeff F hF]
      unfold gen
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
    rw [e] at this
    rw [← this]
    simp [ev, MvPolynomial.aeval_eq_eval]
  have h11 : δ 1 = δ 1 * δ 1 := by rw [← hm, _root_.one_mul]
  have h1 : δ 1 = 1 := by
    by_contra hne
    have h0 : δ 1 = 0 := by
      have : δ 1 * (δ 1 - 1) = 0 := by rw [mul_sub, ← h11]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hne
    have hP0 : P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono (s := Set.range (Int.cast : ℤ → ℚ)) ?_
        (Set.infinite_range_of_injective Int.cast_injective)
      rintro _ ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, IsRoot.def]
      rw [hPe, ← _root_.one_mul (C n - Polynomial.X : ℤ[X]), hm, h0, zero_mul]
    exact hP.ne_zero hP0
  obtain ⟨M, hM⟩ := exists_ext δ Φ hN h1 hm Ω
  have hPP : ev (Φ 2) (C Polynomial.X - Polynomial.X : ℚ[X][X]) = P := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.range (Int.cast : ℤ → ℚ)) ?_
      (Set.infinite_range_of_injective Int.cast_injective)
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [hPe, hN 2 _ (lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)), ← coe_evalRingHom, ev_map]
    congr 1
    simp
  have ha : P.map (algebraMap ℚ Ω) = ((P.aroots Ω).map fun x => Polynomial.X - C x).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hP.map _)
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hac : Multiset.card (P.aroots Ω) = 2 * d := by
    rw [aroots_def, IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map, hPd]
  have hMa : ∀ F, M F = ((P.aroots Ω).map fun x => F.eval x).prod := by
    refine eq_prod_of_mul M (P.aroots Ω) (fun c => ?_) (fun β => ?_)
    · rw [hM 1 _ (by simp), ← _root_.mul_one (C c), ev_homog (hh 1), ev_one δ Φ hN h1, _root_.mul_one, hac]
    · have := congrArg (eval β) ha
      rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_map, ← coe_eval₂RingHom, ← hPP,
        ev_map, hPP] at this
      rw [hM 2]
      · simpa using this
      · exact lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)
  intro F
  have := hMa (F.map (algebraMap ℤ Ω))
  simp only [eval_map_algebraMap] at this
  rw [← this, hM (F.natDegree + 1) _ (Nat.lt_succ_of_le natDegree_map_le),
    hN _ F (Nat.lt_succ_self _), ev_map, Polynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

end GlobalTheory.MulPolyNorm

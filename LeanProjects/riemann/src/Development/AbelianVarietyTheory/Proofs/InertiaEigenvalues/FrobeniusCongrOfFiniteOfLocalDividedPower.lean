import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem coeff_coeff_natCast_mul {K : Type} [CommRing K] (m i n : ℕ) (G : K⟦X⟧⟦X⟧) :
    coeff n (coeff i ((m : K⟦X⟧⟦X⟧) * G)) = (m : K) * coeff n (coeff i G) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

theorem goodSet_of_finite_of_local (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hfin : ∀ (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)),
      ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂)
    (hφ : ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)))
    (hpow : ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (G ^ l)) = coeff n (coeff i (H ^ l))) :
    ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂ := by
  classical
  rintro z ⟨w, rfl⟩
  have key : ∀ p : ℕ × ℕ, ∃ v b : Wq l a, ∀ τ : ZMod a,
      coeff p.2 (coeff p.1 (frob2 φ₂ (ofW t K e w) τ)) =
        algebraMap O K (emb t τ v) / (dpDen e p.1 p.2 : K) ∧
      coeff p.2 (coeff p.1 (frob2 φ₂ (ofW t K e w) τ)) =
        coeff p.2 (coeff p.1 ((ofW t K e w τ) ^ l)) +
          (l : K) * (algebraMap O K (emb t τ b) / (dpDen e p.1 p.2 : K)) := by
    rintro ⟨i, n⟩
    set s : Finset (ℕ × ℕ) := Finset.range (i + 1) ×ˢ Finset.range (n + 1) with hs
    obtain ⟨-, ⟨v, hv⟩, B, ⟨b, rfl⟩, hB⟩ := hfin w s
    have hagree : ∀ τ : ZMod a, ∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' (ofW t K e w τ)) =
        coeff n' (coeff i' (ofW t K e (fun p => if p ∈ s then w p else 0) τ)) := by
      intro τ i' hi n' hn
      have hm : (i', n') ∈ s := by
        simp only [hs, Finset.mem_product, Finset.mem_range]
        omega
      rw [coeff_ofW, coeff_ofW, if_pos hm]
    refine ⟨v (i, n), b (i, n), fun τ => ?_⟩
    have h1 : coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) =
        coeff n (coeff i (frob2 φ₂ (ofW t K e (fun p => if p ∈ s then w p else 0)) τ)) :=
      hφ i n _ _ (hagree (τ - 1))
    refine ⟨?_, ?_⟩
    · rw [h1, ← hv, coeff_ofW]
    · rw [h1, hB, hpow i n _ _ (hagree τ), Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
        map_add, map_add, coeff_coeff_natCast_mul, coeff_ofW]
  choose v b hvb using key
  refine ⟨⟨w, rfl⟩, ⟨v, ?_⟩, ofW t K e b, ⟨b, rfl⟩, ?_⟩
  · funext τ
    ext i n
    rw [coeff_ofW]
    exact ((hvb (i, n) τ).1).symm
  · funext τ
    ext i n
    rw [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
        map_add, map_add, coeff_coeff_natCast_mul, coeff_ofW]
    exact (hvb (i, n) τ).2

end GlobalTheory.CrysPrism

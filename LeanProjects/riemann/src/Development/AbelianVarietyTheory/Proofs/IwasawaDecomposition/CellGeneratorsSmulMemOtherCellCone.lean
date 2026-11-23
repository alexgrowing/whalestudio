import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_smul_eq_sum_of_sum_toReal_eq {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m' → ℝ) (hδ : IsCell bar φ δ) (hγ : IsCell bar φ γ) (hc : ∀ j, 0 ≤ c j)
    (hs : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j)) :
    ∀ i, ∃ (k : ℕ) (a : Fin m' → ℕ), 0 < k ∧ k • δ i = ∑ j, a j • γ j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict

  have hrel : ∑ i, (ℓ (δ i) : ℝ) = ∑ j, c j * (ℓ (γ j) : ℝ) := by
    have e := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim δ γ) (c := Sum.elim (fun _ => (1 : ℝ)) (fun j => -c j)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, one_smul, neg_smul, Finset.sum_neg_distrib, hs,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at e
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul, Finset.sum_neg_distrib] at e
    linarith

  have hlinγ := (linearOn_iff φ γ).1 hγ.linear c hc
  have hlinδ := (linearOn_iff φ δ).1 hδ.linear (fun _ => 1) (fun _ => zero_le_one)
  simp only [one_smul, one_mul] at hlinδ
  rw [hs, hlinγ] at hlinδ

  have hsum : ∑ i, ((ℓ (δ i) : ℝ) - N * φ.evalZ (δ i)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hlinδ, hrel, Finset.mul_sum]
    simp only [h1]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun j _ => by ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (ℓ (δ i) : ℝ) - N * φ.evalZ (δ i) := fun i _ =>
    sub_nonneg.2 (h2 _ (hδ.mem i) (hδ.nonneg i))
  intro i
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  exact h3 _ (hδ.mem i) (hδ.nonneg i) (by linarith)

end GlobalTheory.PolFan

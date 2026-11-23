import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointPrimeToPSimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapHarrisTaylorIntegralModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHeckeMapCompEqForgetLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfCompEtaleSameRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjectiveStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem isSeparated_model_str {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) : IsSeparated M.s := by
  obtain ⟨n, i, hi, -, e⟩ := M.qproj
  have : IsSeparated (PSpace.str R n) := by
    unfold PSpace.str
    infer_instance
  rw [← e]
  infer_instance

theorem exists_heckeMap_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π ∧ IsFinite π ∧ Etale π ∧ Surjective π := by
  intro p _ D R _ _ b g c k N hc hk hN hNp hg hgk hck M M'
  have hp : p.Prime := Fact.out
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      exact absurd (Nat.coprime_zero_left p |>.1 hk) hp.ne_one
    · exact h
  obtain ⟨g', h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.exists_adjoint_primeToP_similitude p D g c k hc hk hg hgk hck
  have h3' : ∀ x y, D.EF (g' x) (g' y) = ((k ^ 2 / c : ℕ) : ℤ) * D.EF x y := by
    intro x y
    rw [h3 x y]
    push_cast
    rfl
  have c1 : (N * k).Coprime p := Nat.Coprime.mul_left hNp hk
  have c2 : (N * k * k).Coprime p := Nat.Coprime.mul_left c1 hk
  have c3 : (N * k * k * k).Coprime p := Nat.Coprime.mul_left c2 hk
  have l1 : 3 ≤ N * k := hN.trans (Nat.le_mul_of_pos_right _ hk0)
  have l2 : 3 ≤ N * k * k := l1.trans (Nat.le_mul_of_pos_right _ hk0)
  have l3 : 3 ≤ N * k * k * k := l2.trans (Nat.le_mul_of_pos_right _ hk0)
  obtain ⟨M₂⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R b (N * k * k) l2 c2
  obtain ⟨M₃⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R b (N * k * k * k) l3 c3
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g c k N hc hk hN hNp hg hgk hck M M'
  obtain ⟨π₁, hπ₁⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g' (k ^ 2 / c) k (N * k) h5 hk l1 c1 h3' h4 h6 M' M₂
  obtain ⟨π₂, hπ₂⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g c k (N * k * k) hc hk l2 c2 hg hgk hck M₂ M₃
  have e : π ≫ M.s = M'.s := hπ.1
  have e₁ : π₁ ≫ M'.s = M₂.s := hπ₁.1
  have e₂ : π₂ ≫ M₂.s = M₃.s := hπ₂.1
  have f1 := GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel p D R b g g' c (k ^ 2 / c) k N hk hN hNp h1 h2 h7 c2 M.toRepFam M'.toRepFam
    M₂.toRepFam π π₁ hπ hπ₁
  have f2 := GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel p D R b g' g (k ^ 2 / c) c k (N * k) hk l1 c1 h2 h1 (by rw [mul_comm, h7]) c3
    M'.toRepFam M₂.toRepFam M₃.toRepFam π₁ π₂ hπ₁ hπ₂
  obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective p D R b N (N * k * k) _ c2 hN M M₂ (π₁ ≫ π)
    (by rw [Category.assoc, e, e₁]) f1
  obtain ⟨-, -, b3⟩ := GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective p D R b (N * k) (N * k * k * k) _ c3 l1 M' M₃ (π₂ ≫ π₁)
    (by rw [Category.assoc, e₁, e₂]) f2
  have s1 : Surjective π₁ := Surjective.of_comp π₂ π₁
  have t1 : Etale π₁ := GlobalTheory.T.etale_of_comp_etale_sameRelativeDimension _ _ _ _ π₁ π M₂.s M'.s _ e₁ M₂.smooth M'.smooth a2
  have hs : IsSeparated π := by
    have : IsSeparated (π ≫ M.s) := e ▸ isSeparated_model_str M'
    exact IsSeparated.of_comp π M.s
  have hl : LocallyOfFiniteType π := by
    have := M'.smooth
    have : Smooth M'.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M'.s
    have : LocallyOfFiniteType (π ≫ M.s) := by rw [e]; infer_instance
    exact locallyOfFiniteType_of_comp π M.s
  obtain ⟨r1, r2⟩ := GlobalTheory.T.etale_isFinite_of_comp_etale_surjective' _ _ _ π₁ π t1 s1 a2 a1 hs hl
  exact ⟨π, hπ, r2, r1, Surjective.of_comp π₁ π⟩

end GlobalTheory.UPel.HT.Hecke

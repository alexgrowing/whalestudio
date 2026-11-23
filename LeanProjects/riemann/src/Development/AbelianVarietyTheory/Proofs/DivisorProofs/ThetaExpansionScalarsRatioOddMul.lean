import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddMultiplicationPullbackThetaFamilyDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionScalarArbitraryOfMembersZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionSecondScalarDeterminedOfNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalarsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem ratio_odd_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (a b : W) (v : Wˣ), a ≠ 0 ∧ b ≠ 0 ∧ T.Exp a b θ₀ F₁ ∧ b * T.φ t = a * T.φ r * v := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁ θ₀ hθ
  by_cases hz : ∀ α j, (F₁.f α).f j = 0
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun W _ _ _ T => ?_⟩
    obtain ⟨a, b, ha, hb, h⟩ := hθ W T
    exact ⟨a, a, 1, ha, ha, GlobalTheory.T.expansion_scalar_arbitrary_of_members_zero R hR D C W T 1 le_rfl θ₀ F₁ hz a b h a, by simp⟩
  push_neg at hz
  obtain ⟨G, S, hG, hS⟩ := GlobalTheory.T.exists_oddMultiplication_pullback_thetaFamily_degree_sq R hR D C m hm F₁ θ₀
  have hGz := hG hz
  have hk : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  by_cases hT : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), Nonempty (Trait C W)
  swap
  · refine ⟨1, 1, one_ne_zero, one_ne_zero, fun W _ _ _ T => (hT ⟨W, _, _, _, ⟨T⟩⟩).elim⟩
  obtain ⟨W₀, _, _, _, ⟨T₀⟩⟩ := hT
  obtain ⟨a₀, b₀, ha₀, hb₀, h₀⟩ := hθ W₀ T₀
  obtain ⟨v₀, hv₀⟩ := hS W₀ T₀ a₀ b₀ ha₀ h₀
  obtain ⟨r, t, hr, ht, hrt⟩ := GlobalTheory.T.exists_ratio_of_expansions_proportional_at_trait R hR D C (m ^ 2) hk G S (Φ G) (fun W _ _ _ T => (hΦ W T).imp fun u hu => hu G)
    W₀ T₀ a₀ (b₀ * v₀) ha₀ (mul_ne_zero hb₀ v₀.ne_zero) hv₀
  refine ⟨r, t, hr, ht, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, h⟩ := hθ W T
  obtain ⟨v, hv⟩ := hS W T a b ha h
  obtain ⟨u, hu⟩ := hrt W T
  have htW : T.φ t ≠ 0 := fun h0 => ht (T.inj (h0.trans (map_zero _).symm))
  have h1 := GlobalTheory.T.coverTrait_expansion_scale_both_scalars R D C W T (m ^ 2) S G a (b * v) (T.φ t) hv
  have h2 := GlobalTheory.T.coverTrait_expansion_scale_both_scalars R D C W T (m ^ 2) S G (T.φ t) (T.φ r * u) a hu
  rw [mul_comm a (T.φ t)] at h2
  have he := GlobalTheory.T.expansion_secondScalar_determined_of_nonzero R hR D C W T (m ^ 2) hk S G hGz (T.φ t * a) _ _ (mul_ne_zero htW ha) h1 h2
  refine ⟨a, b, u * v⁻¹, ha, hb, h, ?_⟩
  have : b * T.φ t * v = a * T.φ r * u := by linear_combination he
  calc b * T.φ t = b * T.φ t * v * ↑v⁻¹ := by simp [mul_assoc]
    _ = _ := by rw [this]; push_cast; ring

end GlobalTheory.Mum

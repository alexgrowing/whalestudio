import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZMatEInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntExtension
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem zMatE_congr_of_entries (X : Data E r) (N : ℕ) (cu : FJ.CuspFD X ρ)
    (c : Fin ρ → FractionalIdeal (𝓞 E)⁰ E)
    (hd : ∀ v ∈ X.Λ, ∀ b, ∀ a' ∈ c b, ∃ n : ℤ,
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v (cu.e b) * cc a') = n)
    (hc : ∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ c b)
    (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : ∀ a b (y : E), (∀ a' ∈ c b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) →
      ∃ z ∈ c a, β a b / X.ξ0 * y = (N : E) * z) :
    ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, FJ.zMatE X cu.e β *ᵥ v = v + N • w := by
  intro v hv
  choose z hz hz' using fun a b => hβ a b _ (hd v hv b)
  refine ⟨∑ a, (∑ b, -z a b) • cu.e a, (hc _).2 fun a => ?_, ?_⟩
  · exact (c a : Submodule (𝓞 E) E).sum_mem fun b _ => (c a : Submodule (𝓞 E) E).neg_mem (hz a b)
  · rw [zMatE_mulVec, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    have h := hz' a b
    have h0 := X.ξ0_ne
    rw [mul_neg, ← h]
    field_simp

theorem mem_zGam_principal_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (D : Datum H) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), LinearMap.range φ = X.Λ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ x) (φ y))) → (∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + N • w) → (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ β, β ∈ FJ.zGam X cu ↔ FJ.IsSkew β ∧ ∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z := by
  intro E _ _ _ H r ρ X N D φ cu c hΛ hφ hΓ hc β
  have hsd := GlobalTheory.SatDual.pairing_pseudoBasis E H D r (-X.ξ0) X.Gm φ ρ cu.e c
    (by rw [cc_neg', X.ξ0_im]) hφ cu.ind (by rw [hΛ]; exact hc)
  have hd : ∀ v ∈ X.Λ, ∀ b, ∀ a' ∈ c b, ∃ n : ℤ,
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v (cu.e b) * cc a') = n := by
    intro v hv
    rw [← hΛ] at hv
    obtain ⟨x, rfl⟩ := hv
    exact (hsd fun b => -X.ξ0 * herm X.Gm (φ x) (cu.e b)).1 ⟨x, fun _ => rfl⟩
  have h0 := X.ξ0_ne
  constructor
  · rintro ⟨hs, γ, hγ, e⟩
    refine ⟨hs, fun a b y hy => ?_⟩
    obtain ⟨x, hx⟩ := (hsd (Pi.single b y)).2 (by
      intro b' a' ha'
      by_cases hb : b' = b
      · subst hb
        simpa using hy a' ha'
      · exact ⟨0, by simp [Pi.single_eq_of_ne hb]⟩)
    obtain ⟨w, hw, hw'⟩ := ((hΓ γ).1 hγ).2 (φ x) (hΛ ▸ ⟨x, rfl⟩)
    rw [e, zMatE_mulVec, add_right_inj] at hw'
    have h1 : ∀ a, ∑ b', β a b' * herm X.Gm (φ x) (cu.e b') = -(β a b / X.ξ0 * y) := by
      intro a
      rw [Finset.sum_eq_single b]
      · have h2 := hx b
        rw [Pi.single_eq_same] at h2
        rw [← h2]
        field_simp
      · intro b' _ hb'
        have h2 := hx b'
        rw [Pi.single_eq_of_ne hb', mul_eq_zero, neg_eq_zero] at h2
        rw [h2.resolve_left h0, mul_zero]
      · simp
    simp only [h1] at hw'
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      rw [zero_smul] at hw'
      have h3 := Fintype.linearIndependent_iff.1 cu.ind _ hw' a
      exact ⟨0, FractionalIdeal.zero_mem _, by rw [mul_zero]; exact neg_eq_zero.1 h3⟩
    · have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
      have h3 : ∑ a, ((N : E)⁻¹ * (β a b / X.ξ0 * y)) • cu.e a = -w := by
        have h4 : w = (N : E)⁻¹ • (N • w) := by
          rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hN', one_smul]
        rw [h4, ← hw', Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_smul, ← neg_smul, mul_neg, neg_neg]
      refine ⟨_, (hc _).1 (h3 ▸ X.Λ.neg_mem hw) a, ?_⟩
      rw [mul_inv_cancel_left₀ hN']
  · rintro ⟨hs, hβ⟩
    have h1 := zMatE_congr_of_entries X N cu c hd hc β hβ
    have h2 := zMatE_congr_of_entries X N cu c hd hc (-β) (by
      intro a b y hy
      obtain ⟨z, hz, hz'⟩ := hβ a b y hy
      refine ⟨-z, (c a : Submodule (𝓞 E) E).neg_mem hz, ?_⟩
      rw [Matrix.neg_apply, neg_div, neg_mul, hz', mul_neg])
    have hm : FJ.zMatE X cu.e β * FJ.zMatE X cu.e (-β) = 1 := by
      rw [← zMatE_add, add_neg_cancel, zMatE_zero]
    have hm' : FJ.zMatE X cu.e (-β) * FJ.zMatE X cu.e β = 1 := by
      rw [← zMatE_add, neg_add_cancel, zMatE_zero]
    refine ⟨hs, ⟨_, _, hm, hm'⟩, (hΓ _).2 ⟨⟨zMatE_unitary X cu β hs, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩, h1⟩, rfl⟩
    · obtain ⟨w, hw, hw'⟩ := h1 x hx
      change FJ.zMatE X cu.e β *ᵥ x ∈ X.Λ
      rw [hw']
      exact X.Λ.add_mem hx (nsmul_mem hw N)
    · obtain ⟨w, hw, hw'⟩ := h2 _ hx
      change FJ.zMatE X cu.e β *ᵥ x ∈ X.Λ at hx
      change FJ.zMatE X cu.e (-β) *ᵥ (FJ.zMatE X cu.e β *ᵥ x) = FJ.zMatE X cu.e β *ᵥ x + _ at hw'
      rw [Matrix.mulVec_mulVec, hm', Matrix.one_mulVec] at hw'
      rw [hw']
      exact X.Λ.add_mem hx (nsmul_mem hw N)

end GlobalTheory.CuspCentre

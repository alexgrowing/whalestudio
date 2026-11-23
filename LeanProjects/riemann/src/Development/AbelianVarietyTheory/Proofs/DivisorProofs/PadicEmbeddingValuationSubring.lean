import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairsSameSimilitude
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistedUnitCommutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugatesAlgebraRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRegularConjugateLocalScalarNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegularStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  intro p _ G _ v _ L f hf K' f' _ β x t hx hreg hβ _ P
  by_cases hne : ∃ y₀ : grp G β, minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P ∧
      ∃ a : Dat G v β, FixL G v β y₀ a.2.1 ∧
        f (a.1.1⁻¹ * toAfF G β x t hx y₀ * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y₀ * a.1.2) ≠ 0
  swap
  · exact ⟨∅, fun y hy ha => absurd ⟨y, hy, ha⟩ hne⟩
  obtain ⟨y₀, hP₀, a₀, hfix₀, ha₀⟩ := hne
  obtain ⟨hdeg₀, hsep₀⟩ := hreg y₀ a₀.1.1 (left_ne_zero_of_mul ha₀) ⟨a₀.2.1, a₀.2.2, hfix₀⟩
  obtain ⟨hy₀, -⟩ := y₀.prop
  obtain ⟨S, hS⟩ := GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm p G L f hf β x t hx hβ y₀ hsep₀ hdeg₀
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G β hβ ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) (((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) hy₀ hsep₀ hdeg₀ S
  have key : ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → ∀ g : G.GAf,
      f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 → ∃ a' ∈ A, ∃ b : Bool, ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = b ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
    intro y hy g hg
    obtain ⟨c, hc⟩ := units_conj_of_minpoly_eq_of_separable G ((y : G.Cˣ × ℚˣ).1) ((y₀ : G.Cˣ × ℚˣ).1)
      (by rw [hy, hP₀]) hsep₀ hdeg₀
    have h2 := GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc
    obtain ⟨hu, hcm, hfix⟩ := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc h2
    obtain ⟨a', ha', r, e, he, hre⟩ := hA _ hu hcm hfix (fun ℓ _ hℓ => hS y g hg c hc ℓ hℓ)
    exact ⟨a', ha', decide (0 < (r : ℚ)), c, r, e, hc, he, rfl, hre⟩
  let D : G.C × Bool → grp G β → Prop := fun ab y => ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = ab.2 ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * ab.1 * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
  let ρ : G.C × Bool → grp G β := fun ab => if h : ∃ y, D ab y then h.choose else 1
  refine ⟨(A ×ˢ (Finset.univ : Finset Bool)).image ρ, ?_⟩
  rintro y hy ⟨a, _, ha⟩
  obtain ⟨a', ha', b, hD⟩ := key y hy a.1.1 (left_ne_zero_of_mul ha)
  have hex : ∃ y, D (a', b) y := ⟨y, hD⟩
  refine ⟨ρ (a', b), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨ha', Finset.mem_univ _⟩), ?_⟩
  have hρ : ρ (a', b) = hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨c', r', e', hc', he', hb', hre'⟩ := hex.choose_spec
  dsimp only at hb' hre'
  obtain ⟨c, r, e, hc, he, hb, hre⟩ := hD
  have h2 : (hex.choose : G.Cˣ × ℚˣ).2 = (y : G.Cˣ × ℚˣ).2 := by
    rw [GlobalTheory.grp_factor_eq_of_conj p G β _ y₀ c' hc', GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc]
  refine GlobalTheory.Div.conj_of_twist p G β hex.choose y ((y₀ : G.Cˣ × ℚˣ).1) c' c (e * e'⁻¹) ((r : ℚ) / r') hc' hc h2 ?_ ?_ ?_
  · rw [Units.val_mul]
    exact he.mul_left he'.units_inv_left
  · have hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)) := by
      rw [← decide_eq_decide, hb, hb']
    rcases lt_or_gt_of_ne r'.ne_zero with h | h
    · have hn : ¬ (0 < (r : ℚ)) := fun h0 => absurd (hr.1 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r.ne_zero) h
    · exact div_pos (hr.2 h) h
  · rw [hre', hre]
    exact conj_rel_alg' G β e e' a' r r'

end GlobalTheory.LKCx.ClsReg

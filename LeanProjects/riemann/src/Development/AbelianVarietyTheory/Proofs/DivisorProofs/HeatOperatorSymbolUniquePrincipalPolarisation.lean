import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOfScaledSectionValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfScaledSectionValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSymbolZeroOfBracketPreservingStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem symbol_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Λ₁ Λ₂ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (d₁ d₂ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u₁ u₂ : Fin n → (FractionRing Ω)) (p₁ p₁' p₂ p₂' : (FractionRing Ω)), Λ₁ᵀ = Λ₁ → Λ₂ᵀ = Λ₂ → (∀ r, d₁ ((algebraMap Ω (FractionRing Ω)) (φ r)) = d₂ ((algebraMap Ω (FractionRing Ω)) (φ r))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₁ (fun a => ⇑(δL a)) Λ₁ u₁ p₁ p₁' k s))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₂ (fun a => ⇑(δL a)) Λ₂ u₂ p₂ p₂' k s))) → Λ₁ = Λ₂ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab n v' D Ω _ _ _ φ x' δ dd' hcomp hx hinv hδ hval hinj g hg δL hδL
    Λ₁ Λ₂ d₁ d₂ u₁ u₂ p₁ p₁' p₂ p₂' hΛ₁ hΛ₂ hd h₁ h₂
  have sub := fun j s s' (hs : GlobalTheory.HeatSym.VS φ t.PP.L x' g j s) (hs' : GlobalTheory.HeatSym.VS φ t.PP.L x' g j s') =>
    GlobalTheory.T.sub_of_scaled_section_values φ t.G.hom t.PP.L x' g hx j s s' hs hs'
  have mul := fun j j' s s' (hs : GlobalTheory.HeatSym.VS φ t.PP.L x' g j s) (hs' : GlobalTheory.HeatSym.VS φ t.PP.L x' g j' s') =>
    GlobalTheory.T.mul_of_scaled_section_values φ t.PP.L t.PP.isLB x' g j j' s s' hs hs'
  have hQ : ∀ (j : ℕ), 1 ≤ j → ∀ s, GlobalTheory.HeatSym.VS φ t.PP.L x' g j s →
      GlobalTheory.HeatSym.VS φ t.PP.L x' g j (ringOp ⇑d₁ (fun a => ⇑(δL a)) Λ₁ u₁ p₁ p₁' j s -
        ringOp ⇑d₂ (fun a => ⇑(δL a)) Λ₂ u₂ p₂ p₂' j s) :=
    fun j hj s hs => sub j _ _ (h₁ j hj s hs) (h₂ j hj s hs)
  have hsym : (Λ₁ - Λ₂)ᵀ = Λ₁ - Λ₂ := by rw [Matrix.transpose_sub, hΛ₁, hΛ₂]
  have hcoe : (fun y => d₁ y - d₂ y) = ⇑(d₁ - d₂) := rfl
  refine sub_eq_zero.mp (GlobalTheory.T.verticalSymbol_zero_of_bracket_preserving E H R t P m tt gam hmon htt hab n v' D Ω φ x' δ dd' hcomp hx hinv hδ hval hinj g hg δL hδL
    (d₁ - d₂) (Λ₁ - Λ₂) hsym (fun r => by rw [Derivation.sub_apply, hd, sub_self]) ?_)
  intro k hk b c hb hc
  have hk2 : 1 ≤ k + k := le_add_right hk
  have hbc := hQ (k + k) hk2 _ (mul k k b c hb hc)
  have hbb := hQ (k + k) hk2 _ (mul k k b b hb hb)
  have hBc := sub _ _ _ (sub _ _ _ hbc (mul k k _ _ hb (hQ k hk c hc))) (mul k k _ _ hc (hQ k hk b hb))
  have hBb := sub _ _ _ (sub _ _ _ hbb (mul k k _ _ hb (hQ k hk b hb))) (mul k k _ _ hb (hQ k hk b hb))
  have hX := sub _ _ _ (mul k (k + k) _ _ hb hBc) (mul k (k + k) _ _ hc hBb)
  simp only [GlobalTheory.HeatSym.ringOp_sub, hcoe] at hX
  have key := GlobalTheory.HeatSym.bracket ⇑(d₁ - d₂) (fun a => ⇑(δL a))
    (fun x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
    (fun a x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
    (fun a x y => map_add _ x y) (Λ₁ - Λ₂) hsym (u₁ - u₂) (p₁ - p₂) (p₁' - p₂') k b c
  rw [key] at hX
  have e3 : 3 * k = k + (k + k) := by ring
  rw [e3]
  exact GlobalTheory.HeatSym.VS.half φ hX

end GlobalTheory.HeatSym

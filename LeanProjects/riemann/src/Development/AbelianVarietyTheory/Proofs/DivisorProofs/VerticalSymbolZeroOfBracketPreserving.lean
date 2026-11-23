import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointAbelianVarietyThroughFormalPoiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreInvariantVectorFieldsAtGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationValueSpacesGenericPointDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondOrderSymbolBracketRescaleByUnitPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSecondOrderSymbolVanishesOfPolarisationStatement

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

def GlobalTheory.HeatSym.derOfFun {F : Type} [Field F] (d : F → F) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = x * d y + y * d x) : Derivation ℤ F F :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' d hadd)) fun x y => by
    simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
    exact hmul x y

theorem GlobalTheory.HeatSym.derOfFun_apply {F : Type} [Field F] (d : F → F) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = x * d y + y * d x) (x : F) : GlobalTheory.HeatSym.derOfFun d hadd hmul x = d x := rfl

theorem GlobalTheory.HeatSym.vertical_symbol_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Λᵀ = Λ → (∀ r, δ₀ ((algebraMap Ω (FractionRing Ω)) (φ r)) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ b c : FractionRing Ω, GlobalTheory.HeatSym.VS φ t.PP.L x' g k b → GlobalTheory.HeatSym.VS φ t.PP.L x' g k c → GlobalTheory.HeatSym.VS φ t.PP.L x' g (3 * k) ((k : FractionRing Ω) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b))) → Λ = 0 := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hloc n v' D Ω _ _ _ φ x' δ dd' hcomp hx' hinv hδ hval
    hsep g hg δL hδL δ₀ Λ hΛ hδ₀ hbr

  obtain ⟨ψ, ξ, hψ, hξ, hξ', hξsep⟩ := GlobalTheory.T.exists_genericPoint_abelianVariety_through_formalPoint E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL
  obtain ⟨v, dd, hinv₂, hval₂⟩ := GlobalTheory.T.generic_fibre_invariant_vectorFields_at_generic_point E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL ψ ξ hψ hξ hξ' hξsep
  obtain ⟨j₀, q, hj₀, hq, hVS⟩ := GlobalTheory.T.polarisation_value_spaces_generic_point_dictionary E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL ψ ξ hψ hξ hξ' hξsep

  have hker : ∀ D' : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      (∀ r, D' (algebraMap Ω (FractionRing Ω) (φ r)) = 0) → ∀ s, D' (ψ s) = 0 := by
    intro D' hD' s
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective R s
    rw [map_div₀, hψ, hψ, Derivation.leibniz_div, hD', hD']
    simp
  have hδL₀ : ∀ a r, δL a (algebraMap Ω (FractionRing Ω) (φ r)) = 0 := by
    intro a r
    rw [hδL, hδ, map_zero]

  have hadd : ∀ x y : FractionRing Ω,
      (δ₀ (x + y) - ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x + y)) =
        (δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) + (δ₀ y - ∑ a, ∑ e, Λ a e * δL a q / q * δL e y) := by
    intro x y
    have : ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x + y) =
        ∑ a, ∑ e, Λ a e * δL a q / q * δL e x + ∑ a, ∑ e, Λ a e * δL a q / q * δL e y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_add, mul_add]
    rw [map_add, this]
    ring
  have hmul : ∀ x y : FractionRing Ω,
      (δ₀ (x * y) - ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x * y)) =
        x * (δ₀ y - ∑ a, ∑ e, Λ a e * δL a q / q * δL e y) + y * (δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) := by
    intro x y
    have : ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x * y) =
        x * ∑ a, ∑ e, Λ a e * δL a q / q * δL e y + y * ∑ a, ∑ e, Λ a e * δL a q / q * δL e x := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, this]
    ring
  let δ₁ := GlobalTheory.HeatSym.derOfFun (fun x => δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) hadd hmul
  have hδ₁ : ∀ x, δ₁ x = δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x := fun x =>
    GlobalTheory.HeatSym.derOfFun_apply _ hadd hmul x
  have hδ₁ψ : ∀ r, δ₁ (ψ r) = 0 := by
    intro r
    rw [hδ₁, hker δ₀ hδ₀ r]
    simp [hker (δL _) (hδL₀ _) r]
  have : CharZero R := algebraRat.charZero R
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))

  let δL' := fun a : Fin n =>
    GlobalTheory.HeatSym.derOfFun (δL a) (fun x y => map_add _ x y)
      (fun x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
  have hδL' : ∀ a x, δL' a x = δL a x := fun a x => GlobalTheory.HeatSym.derOfFun_apply _ _ _ x
  have hval₃ : ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL' a (valR ξ O f) := by
    intro a O f h
    rw [hδL']
    exact hval₂ a O f h

  refine GlobalTheory.T.verticalSecondOrderSymbol_vanishes_of_polarisation (FractionRing R) P.A n v dd hinv₂ (FractionRing Ω) ψ ξ hξ hξsep δL' hval₃ j₀ hj₀ δ₁ Λ hΛ
    hδ₁ψ ?_
  intro k hk σ τ
  have hb := (hVS k _ hk).2 ⟨σ, rfl⟩
  have hc := (hVS k _ hk).2 ⟨τ, rfl⟩
  have h3 := hbr k hk _ _ hb hc
  rw [GlobalTheory.T.secondOrderSymbol_bracket_rescale_by_unit_pow Ω n δ₀ δL Λ q _ _ k hq] at h3
  obtain ⟨ρ, hρ⟩ := (hVS (3 * k) _ (by omega)).1 h3
  refine ⟨ρ, ?_⟩
  rintro b c rfl rfl
  simp only [hδ₁, hδL']
  exact mul_left_cancel₀ (pow_ne_zero _ hq) hρ

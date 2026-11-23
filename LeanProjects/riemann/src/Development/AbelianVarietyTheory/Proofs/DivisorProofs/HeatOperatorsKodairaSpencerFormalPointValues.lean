import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHeatOperatorsAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedHeatOperatorsPreserveSectionsUpToConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeatOperatorValuesRingOperatorFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionFieldMapBasicOpenFormalPointStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatV

theorem heat_values_of_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (iota : Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) →+* (FractionRing Ω)) (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, iota (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = (algebraMap Ω (FractionRing Ω)) (φ r)) ∧ (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (iota.mapMatrix Θ₁) u' p p' k s)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab n v' D Ω _ _ _ φ x' δ dd' hcomp hx' hinv hδ hdd hinj g hg δL hδL
    Θ₁ DV hDV hKS
  have hc : (∏ i, tt i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  obtain ⟨iota, hiota⟩ := GlobalTheory.T.exists_fractionField_map_basicOpen_formalPoint E H R t (∏ i, tt i) hc Ω φ x' hx' hinj
  obtain ⟨J, W, j, d, u, pf, pf', hW, hcov, hle, hfld, hlift, hglue⟩ :=
    GlobalTheory.T.exists_local_heatOperators_abelianLocus E H R t P m tt gam hmon htt hab _ rfl n v' D dd' hinv Θ₁ DV hDV hKS
  obtain ⟨dt, u', p, p', hdt, hval⟩ := GlobalTheory.T.local_heat_operator_values_ring_operator_fraction_field E H R t _ hc n v' D Ω φ x' δ dd' hcomp hx' hinv hδ hdd hinj g hg δL hδL Θ₁ DV hDV
    iota hiota J W j d u pf pf' hW hcov hle hfld hlift hglue
  refine ⟨iota, dt, u', p, p', hiota, hdt, ?_⟩
  rintro k hk s ⟨r0, σ, ω, hr0, hv, hω⟩
  obtain ⟨r, σ', hr, hσ'⟩ := GlobalTheory.T.glued_heat_operators_preserve_sections_up_to_constant E H R t _ hc n dd' (fun a => (hinv a).1) D Θ₁ DV hDV J W j d u pf pf' hW hcov hle hfld
    hlift hglue k σ r0
  obtain ⟨ω', hv', hω'⟩ := hval k hk σ σ' r r0 ω hσ' hv
  refine ⟨r * r0 ^ 2, σ', ω', mul_ne_zero hr (pow_ne_zero _ hr0), hv', ?_⟩
  have hz : ∀ a, δL a ((algebraMap Ω (FractionRing Ω)) (φ r0)) = 0 := fun a => by rw [hδL, hδ, map_zero]
  have hdc := hdt r0
  rw [hω', hω]
  simp only [map_mul, map_pow]
  generalize (algebraMap Ω (FractionRing Ω)) (φ r0) = c at hz hdc ⊢
  have h1 : ∀ a x, δL a (c * x) = c * δL a x := fun a x => by
    rw [Derivation.leibniz, hz, smul_zero, add_zero, smul_eq_mul]
  have h2 : dt (c * s) = c * dt s + s * dt c := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  simp only [ringOp, h1, h2, hdc, Finset.mul_sum]
  have e1 : ∀ a b, iota.mapMatrix Θ₁ a b * (c * δL a (δL b s)) = c * (iota.mapMatrix Θ₁ a b * δL a (δL b s)) :=
    fun a b => by ring
  have e2 : ∀ a, u' a * (c * δL a s) = c * (u' a * δL a s) := fun a => by ring
  simp only [e1, e2, ← Finset.mul_sum]
  ring

end GlobalTheory.HeatV

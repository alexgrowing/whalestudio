import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveRingMapOfPointValuesDetectFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverMemberContainingFractionFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldEqBasicOpenExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionEqValueMulUnitPowFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldCommVectorFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFractionRingOfVectorFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatRingOperatorConjByPowNonzeroStatement

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

namespace GlobalTheory.HeatVal

theorem rsT_self {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) : rsT s O₀ = s := by
  simp [GlobalTheory.KS.rsT]

theorem valR_eq {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom) f := by
  unfold valR; rw [dif_pos h]; rfl

theorem value_opV_ringOp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω)), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ σ' : SecM (𝟙 t.G.left) t.PP.L k) (r a : R) (ω : Ω), (∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i))) → IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ ω' : Ω, IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ (algebraMap Ω (FractionRing Ω)) ω' = (algebraMap Ω (FractionRing Ω)) (φ r) * ((algebraMap Ω (FractionRing Ω)) (φ a) * ringOp ⇑dt (fun b => ⇑(δL b)) (iota.mapMatrix Θ₁) u' p p' k ((algebraMap Ω (FractionRing Ω)) ω) - 2 * (k : (FractionRing Ω)) * (algebraMap Ω (FractionRing Ω)) (φ (D a)) * (algebraMap Ω (FractionRing Ω)) ω) := by
  intro E _ _ _ H R _ _ _ _ _ _ t c hc n v' D Ω _ _ _ φ x' δ dd' hadic hx' hinv hδφ hval hinj g hg δL hδL Θ₁ DV hDV iota hiota J W j d u pf pf' hW hcov hWU hfield hlift hglue
  have hφ : Function.Injective φ := GlobalTheory.T.injective_ringMap_of_pointValues_detect_functions R t.G Ω φ x' hx' hinj
  have hφc : φ c ≠ 0 := fun h => hc (hφ (by rw [h, map_zero]))
  haveI : CharZero Ω := charZero_of_injective_ringHom (φ.comp (algebraMap ℚ R)).injective
  haveI : CharZero (FractionRing Ω) :=
    charZero_of_injective_ringHom (IsFractionRing.injective Ω (FractionRing Ω))
  obtain ⟨i0, hi0⟩ := GlobalTheory.T.exists_cover_member_containing_fractionField_point R t.G Ω φ x' hx' c hφc J W hcov
  obtain ⟨dt0, hdt0⟩ := GlobalTheory.T.exists_derivation_fractionRing_of_vectorField t.G.left Ω x' hinj (W i0) (d i0) (hfield i0) hi0
  have hddv := fun a => GlobalTheory.T.pointValue_fractionField_comm_vectorField t.G.left Ω x' (dd' a) (δ a) (δL a) (hinv a).1 (hval a) (hδL a)
  have hcst := GlobalTheory.T.pointValue_fractionField_eq_basicOpen_extension R t.G Ω φ x' hx' c iota hiota (W i0) (hW i0) hi0
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.chartFunction_eq_value_mul_unit_pow_fractionField t.G.left t.PP.L t.PP.isLB Ω x' g (j i0) (W i0) (hWU i0) hi0
  set ψ : Γ(t.G.left, W i0) →+* FractionRing Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp
      ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x').appLE (W i0) ⊤ hi0).hom with hψ
  have hv : ∀ f, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') (W i0) f = ψ f :=
    fun f => valR_eq _ _ hi0 f
  have hd0 : ∀ F, ψ (d i0 (W i0) F) = dt0 (ψ F) := by
    intro F; rw [← hv, ← hv]; exact hdt0 _ _ le_rfl hi0
  have hdd : ∀ a F, ψ (dd' a (W i0) F) = δL a (ψ F) := by
    intro a F; rw [← hv, ← hv]; exact hddv a _ _ hi0
  have hc' : ∀ θ, ψ (GlobalTheory.HeatV.cst t.G.hom _ (hW i0) θ) = iota θ := by
    intro θ; rw [← hv]; exact hcst θ
  obtain ⟨dt, u', p, p', hdt, hgauge⟩ := GlobalTheory.T.heatRingOperator_conj_by_pow_nonzero Ω n dt0 δL (iota.mapMatrix Θ₁) two_ne_zero
    (fun a => iota (u a)) (ψ (pf i0)) (ψ (pf' i0)) (e₀ : FractionRing Ω) e₀.ne_zero
  have hdtR : ∀ r, dt (algebraMap Ω (FractionRing Ω) (φ r)) = algebraMap Ω (FractionRing Ω) (φ (D r)) := by
    intro r
    rw [hdt _ (fun a => by rw [hδL, hδφ, map_zero]), ← hiota, ← hiota, ← hc', ← hc', ← hd0]
    have := hlift i0 (W i0) le_rfl (GlobalTheory.HeatV.resV R c r)
    rw [this, hDV]
  refine ⟨dt, u', p, p', hdtR, ?_⟩
  intro k hk σ σ' r a ω hσ' hω
  have hop : ∀ F, ψ (GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i0) (pf i0) (pf' i0) k (W i0) (hW i0) F) =
      ringOp ⇑dt0 (fun b => ⇑(δL b)) (iota.mapMatrix Θ₁) (fun a => iota (u a)) (ψ (pf i0)) (ψ (pf' i0)) k (ψ F) := by
    intro F
    simp only [GlobalTheory.HeatV.opV, ringOp, map_add, map_sub, map_mul, map_sum, map_natCast, map_ofNat, map_pow, hd0, hdd,
      hc', rsT_self, RingHom.mapMatrix_apply, Matrix.map_apply]
  obtain ⟨ω', hω'⟩ := GlobalTheory.T.exists_sectionValue_in_frame_localRing_point t.G.left t.PP.L t.PP.isLB Ω x' g hg k σ'
  refine ⟨ω', hω', ?_⟩
  have h1 := he₀ k σ ω hω
  have h2 := he₀ k σ' ω' hω'
  rw [hv] at h1 h2
  have h3 := congrArg ψ (hσ' i0)
  simp only [map_mul, map_sub, map_natCast, map_ofNat, hop, hc', hiota] at h3
  rw [h1, h2, mul_comm (algebraMap Ω (FractionRing Ω) ω) ((e₀ : FractionRing Ω) ^ k), hgauge] at h3
  apply mul_left_cancel₀ (pow_ne_zero k e₀.ne_zero)
  linear_combination h3

end GlobalTheory.HeatVal

import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Formalism.LocalToGlobal.ProjectiveLattices.PowMapMemOfPowMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorOnRingConjPowFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueInFrameLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValueAtPointEqRingOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValuesOfSectionsCompleteLocalRingStatement
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

namespace GlobalTheory.Heat

theorem ringOp_map_of_intertwine {A B : Type} [CommRing A] [CommRing B] (iK : A →+* B) {n : ℕ} (d : A → A) (dd : Fin n → A → A)
    (d' : B → B) (dd' : Fin n → B → B) (hd : ∀ w, d' (iK w) = iK (d w)) (hdd : ∀ a w, dd' a (iK w) = iK (dd a w))
    (Θ : Matrix (Fin n) (Fin n) A) (u : Fin n → A) (p p' : A) (k : ℕ) (f : A) :
    iK (ringOp d dd Θ u p p' k f) = ringOp d' dd' (iK.mapMatrix Θ) (fun a => iK (u a)) (iK p) (iK p') k (iK f) := by
  simp only [ringOp, map_sub, map_add, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd,
    RingHom.mapMatrix_apply, Matrix.map_apply]

theorem ringOp_mul_of_const {K : Type} [CommRing K] {n : ℕ} (d : K → K) (δ : Fin n → K → K)
    (Θ : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (p p' : K) (k : ℕ) (c s : K)
    (hd : d (c * s) = c * d s + s * d c) (h1 : ∀ a y, δ a (c * y) = c * δ a y) :
    ringOp d δ Θ u p p' k (c * s) = c * ringOp d δ Θ u p p' k s + 2 * (k : K) * d c * s := by
  simp only [ringOp, h1, hd, mul_left_comm _ c, ← Finset.mul_sum]
  try ring

theorem exists_derivation_fractionRing_ext (Ω : Type) [CommRing Ω] [IsDomain Ω] (d : Derivation ℤ Ω Ω) :
    ∃ dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ w, dL (algebraMap Ω (FractionRing Ω) w) = algebraMap Ω (FractionRing Ω) (d w) := by
  obtain ⟨δ', hder, hδ'⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (nonZeroDivisors Ω) (B := FractionRing Ω)
    (fun w => algebraMap Ω (FractionRing Ω) (d w)) (fun a b => by simp)
    (fun a b => by simp [Derivation.leibniz, smul_eq_mul])
  have hsm : ∀ (z : ℤ) (a : FractionRing Ω), δ' (z • a) = z • δ' a := by
    intro z a
    induction z using Int.induction_on with
    | zero => simp [hder.der_zero]
    | succ i ih => simp only [add_smul, one_smul, hder.add, ih]
    | pred i ih => simp only [sub_smul, one_smul, hder.der_sub, ih]
  have hint : ∀ m : ℤ, δ' (m : FractionRing Ω) = 0 := fun m => by
    have := hsm m 1
    rw [zsmul_eq_mul, _root_.mul_one, hder.der_one] at this
    simpa using this
  have hlb : ∀ a b : FractionRing Ω, δ' (a * b) = a • δ' b + b • δ' a := fun a b => by
    rw [hder.mul, smul_eq_mul, smul_eq_mul]
  let dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω) := { toFun := δ', map_add' := hder.add, map_smul' := fun m y => by rw [RingHom.id_apply, Algebra.smul_def, eq_intCast, zsmul_eq_mul, hder.mul, hint m, MulZeroClass.mul_zero, add_zero], map_one_eq_zero' := hder.der_one, leibniz' := hlb }
  exact ⟨dL, hδ'⟩

theorem heat_acts_on_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) u' p p' k s)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmono htt hab
  intro Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω _ _ _ φ x x' δ hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg δL hδL
  letI := H.starRing
  have hDφ := (GlobalTheory.T.heatOperator_value_at_point_eq_ringOperator R Y.H _ _ P.D.toPre.P.L n dd ⇑D h i0 Ω φ x hx δ hδ dΩ hW hdΩ).1
  obtain ⟨e, p0, p0', hcore⟩ := GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring E H R t P m tt gam hmono htt hab Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω φ x x' δ
    hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg
  obtain ⟨dL, hdL⟩ := exists_derivation_fractionRing_ext Ω dΩ
  set iK := algebraMap Ω (FractionRing Ω) with hiK
  have hiKinj : Function.Injective iK := IsFractionRing.injective Ω (FractionRing Ω)
  have h2R : IsUnit (2 : R) := by
    have := (isUnit_iff_ne_zero.2 (two_ne_zero : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
    rwa [map_ofNat] at this
  have h2K : (2 : FractionRing Ω) ≠ 0 := by
    have := (h2R.map (iK.comp φ)).ne_zero
    rwa [map_ofNat] at this
  have hsymm : ((iK.comp φ).mapMatrix h.Θ)ᵀ = (iK.comp φ).mapMatrix h.Θ := by
    show (h.Θ.map _)ᵀ = h.Θ.map _
    rw [← Matrix.transpose_map, h.symm]
  have hce : iK ((e⁻¹ : Ωˣ) : Ω) ≠ 0 := fun h0 => (e⁻¹).ne_zero (hiKinj (h0.trans (map_zero iK).symm))
  obtain ⟨d', u'', q, q', hd'c, hconj⟩ := GlobalTheory.T.heatOperatorOnRing_conj_pow_fractionField Ω n dL δL ((iK.comp φ).mapMatrix h.Θ) hsymm h2K
    (fun a => iK (φ (h.u a))) (iK p0) (iK p0') _ hce
  refine ⟨d', u'', q, q', fun r => ?_, ?_⟩
  · rw [hd'c _ (fun a => by rw [hδL, hδφ, map_zero]), hdL, hDφ]
  intro k hk s ⟨r₁, σ, ω, hr₁, hv, hs⟩
  obtain ⟨r₂, σ₂, ω₂, hr₂, hv₂, hω₂⟩ := hcore k hk σ ω hv
  have key : iK ω₂ = iK (φ r₂) * ringOp ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK ω) := by
    rw [hω₂, map_mul, map_mul, map_pow, ringOp_map_of_intertwine iK _ _ _ _ hdL hδL, map_mul, map_pow]
    have e1 : iK.mapMatrix (φ.mapMatrix h.Θ) = (iK.comp φ).mapMatrix h.Θ := by
      ext a b; simp
    rw [e1, hconj, ← _root_.mul_assoc (iK (e : Ω) ^ k), ← mul_pow, ← map_mul, Units.mul_inv, map_one, one_pow, _root_.one_mul]
  by_cases hc1 : φ r₁ = 0
  · exact ⟨r₁, σ, ω, hr₁, hv, by rw [hs, hc1]; simp⟩
  · have hδc : ∀ a, δL a (iK (φ r₁)) = 0 := fun a => by rw [hδL, hδφ, map_zero]
    have hdc : d' (iK (φ r₁)) = iK (φ (D r₁)) := by rw [hd'c _ hδc, hdL, hDφ]
    have hs' : iK ω = iK (φ r₁) * s := hs
    have hRO := ringOp_mul_of_const ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK (φ r₁)) s
      (by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]) (fun a y => by
        rw [Derivation.leibniz, hδc, smul_zero, add_zero, smul_eq_mul])
    rw [← hs', hdc] at hRO
    obtain ⟨σ₃, hv₃⟩ := GlobalTheory.T.sectionValueInFrame_linearCombination R t.G t.PP.L Ω φ x' hx' g k σ₂ σ ω₂ ω r₁ (-(2 * (k : R)) * D r₁ * r₂) hv₂ hv
    refine ⟨r₁ * r₁ * r₂, σ₃, _, mul_ne_zero (mul_ne_zero hr₁ hr₁) hr₂, hv₃, ?_⟩
    simp only [RingHom.comp_apply, map_add, map_mul, map_neg, map_natCast, map_ofNat]
    rw [key, hRO, hs']
    ring

end GlobalTheory.Heat

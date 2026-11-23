import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetsOfParOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AltSumMultilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option autoImplicit false
noncomputable section

open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CombInd.Tens

theorem commGroup_coboundary_relation_identity {G : Type} [CommGroup G] (a b x y z : G) : a * b * z⁻¹ = a * x⁻¹ * (b * y⁻¹) * (x * y * z⁻¹) := by
  rw [show a * x⁻¹ * (b * y⁻¹) * (x * y * z⁻¹) = a * b * z⁻¹ * (x⁻¹ * x) * (y⁻¹ * y) by ac_rfl]
  simp

theorem group_pow_mul_identity {G : Type} [CommGroup G] (x y z r₁ r₂ : G) (m : ℕ) :
    z⁻¹ ^ m * (r₁ * r₂) = x⁻¹ ^ m * r₁ * (y⁻¹ ^ m * r₂) * (x * y * z⁻¹) ^ m := by
  rw [mul_pow, mul_pow, show x⁻¹ ^ m * r₁ * (y⁻¹ ^ m * r₂) * (x ^ m * y ^ m * z⁻¹ ^ m) =
    z⁻¹ ^ m * (r₁ * r₂) * (x⁻¹ ^ m * x ^ m) * (y⁻¹ ^ m * y ^ m) by ac_rfl]
  simp

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem prod_expo_add (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (w₁ w₂ : Sym E →₀ ℤ) :
    (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (w₁ + w₂) x) =
      (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w₁ x) * ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w₂ x := by
  rw [LineTest.expo_add, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun x _ => zpow_add _ _ _

theorem unitAt_prod (w : Sym E →₀ ℤ) (b : Y.Y.X) :
    UnitAt b (((∏ x : Letter Dw, (Y.gr_spec b).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf Y (expo Dw w)) b)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
  have := (Base.isEqn_eqn (divOf Y (expo Dw w)) b).iff_unitAt.1 (LineTest.isEqn_divOf Y (expo Dw w) b)
  rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this

theorem lgOf_add (w₁ w₂ : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    lgOf Y (w₁ + w₂) v ε y = lgOf Y w₁ v ε y + lgOf Y w₂ v ε y +
      Real.log (ε.w (TrueGeo.valAt y.1 ((eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1) *
        (eqn (divOf Y (expo Dw (w₁ + w₂))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) := by
  classical
  have hp := LineTest.residueCharacteristic_prime v
  have U₁ := unitAt_prod Y w₁ (below y.1)
  have U₂ := unitAt_prod Y w₂ (below y.1)
  have hE : (divOf Y (expo Dw (w₁ + w₂))).IsEqn (below y.1)
      (eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1)) := by
    rw [LineTest.expo_add, LineTest.divOf_add]; exact (Base.isEqn_eqn _ _).add (Base.isEqn_eqn _ _)
  have Uc : UnitAt (below y.1) ((eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1) *
      (eqn (divOf Y (expo Dw (w₁ + w₂))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := (Base.isEqn_eqn _ _).iff_unitAt.1 hE
    rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
  simp only [lgOf, dif_pos hp]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring), prod_expo_add Y _ w₁ w₂,
    commGroup_coboundary_relation_identity _ _ (eqn (divOf Y (expo Dw w₁)) (below y.1)) (eqn (divOf Y (expo Dw w₂)) (below y.1)) _]
  generalize (∏ x : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w₁ x) *
    (eqn (divOf Y (expo Dw w₁)) (below y.1))⁻¹ = u₁ at U₁ ⊢
  generalize (∏ x : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w₂ x) *
    (eqn (divOf Y (expo Dw w₂)) (below y.1))⁻¹ = u₂ at U₂ ⊢
  generalize eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1) *
      (eqn (divOf Y (expo Dw (w₁ + w₂))) (below y.1))⁻¹ = c at Uc ⊢
  rw [Units.val_mul (u₁ * u₂) c, Units.val_mul u₁ u₂, SmallSec.valAt_mul (U₁.mul U₂).regAt Uc.regAt,
    SmallSec.valAt_mul U₁.regAt U₂.regAt, map_mul, map_mul,
    Real.log_mul (mul_ne_zero (ε.w.pos (SmallSec.valAt_ne_zero U₁)).ne' (ε.w.pos (SmallSec.valAt_ne_zero U₂)).ne')
      (ε.w.pos (SmallSec.valAt_ne_zero Uc)).ne',
    Real.log_mul (ε.w.pos (SmallSec.valAt_ne_zero U₁)).ne' (ε.w.pos (SmallSec.valAt_ne_zero U₂)).ne']
  ring

end Free

theorem a3field_of_a2indep_of_a3one {K : Type} [Field K] (f g₁ g₂ r₁ r₂ : K) (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) (m : ℕ) :
    f * (r₁ * r₂) = f * (g₁ * g₂) ^ m * (g₁⁻¹ ^ m * r₁) * (g₂⁻¹ ^ m * r₂) := by
  rw [mul_pow, inv_pow, inv_pow]
  field_simp

set_option maxHeartbeats 1000000 in

theorem induced_tens : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (m : ℕ+) (R : ℝ) (w₁ w₂ : Sym D.host.E →₀ ℤ) (L₁ L₂ : GlobalTheory.HermLB M.p), (∀ a ∈ w₁.support, a.2.1 = some R) → (∀ a ∈ w₂.support, a.2.1 = some R) → (adlOf (Φ.C k) (metsOf x Φ k) w₁).Induced M L₁ m 0 → (adlOf (Φ.C k) (metsOf x Φ k) w₂).Induced M L₂ m 0 → (adlOf (Φ.C k) (metsOf x Φ k) (w₁ + w₂)).Induced M (L₁.tens L₂) m 0 := by
  intro D A N j S κ s x Φ k M m R w₁ w₂ L₁ L₂ hw₁ hw₂ h₁ h₂
  classical
  obtain ⟨-, r₁, hr₁, hinf₁, hv₁⟩ := h₁
  obtain ⟨-, r₂, hr₂, hinf₂, hv₂⟩ := h₂
  refine ⟨by simp, fun i => r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2), ?_, ?_, ?_⟩
  · dsimp only [adlOf] at hr₁ hr₂ ⊢
    rw [LineTest.expo_add, LineTest.divOf_add, nsmul_add]
    exact GlobalTheory.LineNorm.Add.presents_tens L₁.isLB L₂.isLB M.j hr₁ hr₂
  · intro σ y y' i f hy hi hf
    dsimp only [adlOf] at hinf₁ hinf₂ hf hr₁ hr₂ ⊢
    have hw : ∀ a ∈ (w₁ + w₂).support, a.2.1 = some R := fun a ha =>
      (Finset.mem_union.1 (Finsupp.support_add ha)).elim (hw₁ a) (hw₂ a)
    rw [metsOf_parOf x Φ k σ hw]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul]
    have cA : under y ∈ (L₁.B.pull M.j).U (fun _ => (i PUnit.unit).1) :=
      Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hi PUnit.unit).1
    have cB : under y ∈ (L₂.B.pull M.j).U (fun _ => (i PUnit.unit).2) :=
      Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hi PUnit.unit).2
    obtain ⟨g₁, hg₁⟩ := (divOf (Φ.C k) (expo S.Dw w₁)).exists_isEqn (under y)
    obtain ⟨g₂, hg₂⟩ := (divOf (Φ.C k) (expo S.Dw w₂)).exists_isEqn (under y)
    have hG : (divOf (Φ.C k) (expo S.Dw (w₁ + w₂))).IsEqn (under y) (g₁ * g₂) := by
      rw [LineTest.expo_add, LineTest.divOf_add]; exact hg₁.add hg₂
    have gen {Δ : (Φ.C k).Y.Dv} {g : (Φ.C k).Y.Fnˣ} (hg : Δ.IsEqn (under y) g) (p : ℕ) :
        (p • Δ).GeneratesAt (under y) (((g : (Φ.C k).Y.Fn))⁻¹ ^ p) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 (hg.nsmul p)
      rwa [Units.val_pow_eq_pow_val, ← inv_pow] at this
    have gen1 {Δ : (Φ.C k).Y.Dv} {g : (Φ.C k).Y.Fnˣ} (hg : Δ.IsEqn (under y) g) :
        Δ.GeneratesAt (under y) ((g : (Φ.C k).Y.Fn))⁻¹ := CartierDiv.isEqn_iff_generatesAt_inv.1 hg
    have e₁ := hinf₁ σ y y' _ _ hy cA (gen hg₁ m).regularAt
    have e₂ := hinf₂ σ y y' _ _ hy cB (gen hg₂ m).regularAt
    rw [metsOf_parOf x Φ k σ hw₁] at e₁
    rw [metsOf_parOf x Φ k σ hw₂] at e₂
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul] at e₁ e₂
    rw [(cxSt D.what₂.LL).pn_mPow _ σ _ _ _ _ y (gen1 hg₁)] at e₁
    rw [(cxSt D.what₂.LL).pn_mPow _ σ _ _ _ _ y (gen1 hg₂)] at e₂
    have u₁ := (hr₁.isEqn _ _ cA).generatesAt_iff.1 (gen hg₁ m)
    have u₂ := (hr₂.isEqn _ _ cB).generatesAt_iff.1 (gen hg₂ m)
    have ha : RegAt (under y) (f * ((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) ^ (m : ℕ)) := by
      have := (hG.nsmul _).regularAt_iff.1 hf
      rwa [Units.val_pow_eq_pow_val] at this
    have h₂ := (cxSt D.what₂.LL).pn_mul _ σ _ ((cxSt D.what₂.LL).mPow _ σ _ (m : ℕ)
      (metsOf x Φ k (some R) σ (expo S.Dw (w₁ + w₂)))) _ _ y ha (gen hG m).regularAt
    have hcanc : f * ((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) ^ (m : ℕ) *
        (((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))⁻¹ ^ (m : ℕ) = f := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (g₁ * g₂).ne_zero, one_pow, mul_one]
    rw [hcanc, (cxSt D.what₂.LL).pn_mPow _ σ _ _ _ _ y (gen1 hG)] at h₂
    have hsplit : (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k (some R) σ (expo S.Dw (w₁ + w₂)))
        ((cxSt D.what₂.LL).cx _ σ (((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))⁻¹) y =
        (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k (some R) σ (expo S.Dw w₁))
          ((cxSt D.what₂.LL).cx _ σ ((g₁ : (Φ.C k).Y.Fn))⁻¹) y *
        (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k (some R) σ (expo S.Dw w₂))
          ((cxSt D.what₂.LL).cx _ σ ((g₂ : (Φ.C k).Y.Fn))⁻¹) y := by
      rw [Units.val_mul, mul_inv, ← (cxSt D.what₂.LL).pn_mAdd _ σ _ _ _ _ _ _ y (gen1 hg₁).regularAt
        (gen1 hg₂).regularAt, LineTest.expo_add]
      exact congrFun (congrFun (pn_metsOf_add x Φ k (some R) σ _ _) _) y
    have hf' : f * ((r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2) : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) =
        f * ((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) ^ (m : ℕ) *
          (((g₁ : (Φ.C k).Y.Fn))⁻¹ ^ (m : ℕ) * (r₁ (fun _ => (i PUnit.unit).1) : (Φ.C k).Y.Fn)) *
          (((g₂ : (Φ.C k).Y.Fn))⁻¹ ^ (m : ℕ) * (r₂ (fun _ => (i PUnit.unit).2) : (Φ.C k).Y.Fn)) := by
      simp only [Units.val_mul]
      exact a3field_of_a2indep_of_a3one _ _ _ _ _ g₁.ne_zero g₂.ne_zero _
    rw [h₂, hsplit, hf', ratVal_mul (ha.mul u₁.regAt) u₂.regAt, ratVal_mul ha u₁.regAt, mul_pow, e₁, e₂]
    change _ = _ * Real.exp (-((L₁.φ _).φ (i PUnit.unit).1 y' + (L₂.φ _).φ (i PUnit.unit).2 y'))
    rw [neg_add, Real.exp_add, norm_mul, norm_mul, mul_pow, mul_pow]
    ring
  · intro v e y yt i h hi
    dsimp only [adlOf] at hv₁ hv₂ hr₁ hr₂ ⊢
    have hi₁ : ⊤ ≤ yt ⁻¹ᵁ L₁.B.U (i PUnit.unit).1 := fun x hx => (hi hx).1
    have hi₂ : ⊤ ≤ yt ⁻¹ᵁ L₂.B.U (i PUnit.unit).2 := fun x hx => (hi hx).2
    have e₁ := hv₁ v e y yt (fun _ => (i PUnit.unit).1) h hi₁
    have e₂ := hv₂ v e y yt (fun _ => (i PUnit.unit).2) h hi₂
    have q₁ := GlobalTheory.LineNorm.Add.unitAt_quot (i := fun _ => (i PUnit.unit).1)
      (fun z => Base.isEqn_eqn (divOf (Φ.C k) (expo S.Dw w₁)) z) hr₁ h hi₁
    have q₂ := GlobalTheory.LineNorm.Add.unitAt_quot (i := fun _ => (i PUnit.unit).2)
      (fun z => Base.isEqn_eqn (divOf (Φ.C k) (expo S.Dw w₂)) z) hr₂ h hi₂
    have hE : (divOf (Φ.C k) (expo S.Dw (w₁ + w₂))).IsEqn (below y.1)
        (eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1) * eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1)) := by
      rw [LineTest.expo_add, LineTest.divOf_add]; exact (Base.isEqn_eqn _ _).add (Base.isEqn_eqn _ _)
    have Uc : UnitAt (below y.1) ((eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1) *
        eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1) *
        (eqn (divOf (Φ.C k) (expo S.Dw (w₁ + w₂))) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) := by
      have := (Base.isEqn_eqn _ _).iff_unitAt.1 hE
      rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
    rw [lgOf_add, group_pow_mul_identity (eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1))
      (eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1))]
    simp only [Pi.zero_apply, mul_zero, sub_zero] at e₁ e₂ ⊢
    generalize (eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1))⁻¹ ^ (m : ℕ) * r₁ (fun _ => (i PUnit.unit).1) = u₁
      at q₁ e₁ ⊢
    generalize (eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1))⁻¹ ^ (m : ℕ) * r₂ (fun _ => (i PUnit.unit).2) = u₂
      at q₂ e₂ ⊢
    generalize eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1) * eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1) *
      (eqn (divOf (Φ.C k) (expo S.Dw (w₁ + w₂))) (below y.1))⁻¹ = c at Uc ⊢
    have w₁p := (e.w.pos (SmallSec.valAt_ne_zero q₁)).ne'
    have w₂p := (e.w.pos (SmallSec.valAt_ne_zero q₂)).ne'
    have wcp := (e.w.pos (SmallSec.valAt_ne_zero Uc)).ne'
    rw [Units.val_mul (u₁ * u₂) (c ^ (m : ℕ)), Units.val_mul u₁ u₂, Units.val_pow_eq_pow_val,
      SmallSec.valAt_mul (q₁.mul q₂).regAt (InducedPow.unitAt_pow Uc _).regAt,
      SmallSec.valAt_mul q₁.regAt q₂.regAt, SmallSec.valAt_pow Uc.regAt, map_mul, map_mul, map_pow,
      Real.log_mul (mul_ne_zero w₁p w₂p) (pow_ne_zero _ wcp), Real.log_mul w₁p w₂p, Real.log_pow]
    push_cast
    linear_combination e₁ + e₂

end GlobalTheory.CombInd.Tens

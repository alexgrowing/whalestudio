import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.SteinIso

section General

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_log_normSq (a : Γ(Y, ⊤)) {z : CxPts q σ} (h : CxPts.ev q σ ⊤ a z ≠ 0) :
    CInfAt (fun w => Real.log (‖CxPts.ev q σ ⊤ a w‖ ^ 2)) z := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ ℂ ()).norm_sq ℂ
  exact ⟨⊤, Unit, inferInstance, fun _ => a, fun v => Real.log (‖v ()‖ ^ 2), {v | ‖v ()‖ ^ 2 ≠ 0},
    mem_ptsIn_top, isOpen_ne_fun hs.continuous continuous_const, pow_ne_zero _ (norm_ne_zero_iff.2 h),
    hs.contDiffOn.log fun _ h => h, Filter.EventuallyEq.rfl⟩

def cj (y : CxPts p σ) : CxPts p ((starRingEnd ℂ).comp σ) :=
  ⟨spMap (starRingEnd ℂ) ≫ y.1, by rw [Category.assoc, y.2, ← Spec.map_comp]; rfl⟩

theorem cj_mem {y : CxPts p σ} {U : X.Opens} (h : y ∈ ptsIn p σ U) : cj y ∈ ptsIn p _ U := by
  rw [mem_ptsIn] at h ⊢
  change y.1 (spMap (starRingEnd ℂ) (IsLocalRing.closedPoint ℂ)) ∈ U
  rwa [Subsingleton.elim (spMap (starRingEnd ℂ) (IsLocalRing.closedPoint ℂ)) (IsLocalRing.closedPoint ℂ)]

theorem ratVal_pow [IsIntegral X] {y : CxPts p σ} {f : X.functionField} (hf : UnitAt (under y) f) (m : ℕ) :
    UnitAt (under y) (f ^ m) ∧ ratVal (f ^ m) y = ratVal f y ^ m := by
  induction m with
  | zero =>
    have h := gen_mem (show under y ∈ (⊤ : X.Opens) from trivial)
    have e : (1 : X.functionField) = fnOf ⊤ h (1 : Γ(X, ⊤)ˣ).val := (map_one _).symm
    rw [pow_zero, pow_zero, e]
    exact ⟨unitAt_fnOf (U := ⊤) trivial _ _, by rw [ratVal_fnOf mem_ptsIn_top, Units.val_one, ev_one mem_ptsIn_top]⟩
  | succ m ih => exact ⟨by rw [pow_succ]; exact ih.1.mul hf, by
      rw [pow_succ, ratVal_mul ih.1.regAt hf.regAt, ih.2, pow_succ]⟩

theorem gm_ext [IsIntegral X] {x : X} {s t : (X.presheaf.stalk x)ˣ}
    (h : Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom s =
      Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom t) : s = t :=
  Units.ext (IsFractionRing.injective (X.presheaf.stalk x) X.functionField (congrArg Units.val h))

theorem val_map_gm [IsIntegral X] {x : X} {U : X.Opens} (hx : x ∈ U) (u : Γ(X, U)ˣ) :
    (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom (gm (𝟙 X) x U u)).val =
      fnOf U (gen_mem hx) u.val :=
  (congrArg (algebraMap (X.presheaf.stalk x) X.functionField) (gm_val (𝟙 X) x U hx u)).trans
    (algebraMap_germ hx u.val)

theorem exists_isometric_pull [IsIntegral X] (ρ : X ⟶ Y) (hρ : ρ ≫ q = p) (L : HermLB p)
    (r : L.B.ι → X.functionFieldˣ) (hr : IsRatSec L.B r)
    (hoff : ∀ (σ : k →+* ℂ) (y : CxPts p σ), y ∈ offSupp p σ (L.div hr))
    (hc : ∀ σ, ∃ a : ℝ, ∀ y : CxPts p σ, logNorm (L.φ σ) r y = a) (m : ℕ) (g : X.functionFieldˣ)
    (a b : Γ(Y, ⊤)) (ha : ∀ σ (z : CxPts q σ), CxPts.ev q σ ⊤ a z ≠ 0)
    (hb : ∀ σ (z : CxPts q σ), CxPts.ev q σ ⊤ b z ≠ 0)
    (hg : ∀ h, (g : X.functionField) * fnOf (ρ ⁻¹ᵁ ⊤) h (ρ.app ⊤ b) = fnOf (ρ ⁻¹ᵁ ⊤) h (ρ.app ⊤ a))
    (hd : m • L.div hr = CartierDiv.principal g) :
    ∃ M : HermLB q, (L.pow m).Isometric (M.pull ρ hρ) := by
  choose c hc using hc
  have hu : ∀ i, ∀ x ∈ L.B.U i, UnitAt x ((g : X.functionField) / (r i ^ m : X.functionFieldˣ)) := fun i x hx => by
    have h₁ := ((presents_divOfRatSec L.isLB hr).isEqn i x hx).nsmul m
    refine h₁.iff_unitAt.1 ?_
    erw [hd]
    exact CartierDiv.isEqn_principal _ _
  choose u hu' using fun i => exists_unit_fnOf_eq (hu i)
  let A : ∀ σ, CxPts q σ → ℝ := fun σ z =>
    Real.log (‖CxPts.ev q σ ⊤ a z‖ ^ 2) + -Real.log (‖CxPts.ev q σ ⊤ b z‖ ^ 2)
  have hA : ∀ σ σ' (z : CxPts q σ) (z' : CxPts q σ'), z'.1 = spMap (starRingEnd ℂ) ≫ z.1 → A σ' z' = A σ z :=
    fun σ σ' z z' h => by
      simp only [A, ev_conj h mem_ptsIn_top, RCLike.norm_conj]
  have key : ∀ σ i (y : CxPts p σ), y ∈ ptsIn p σ (L.B.U i) →
      A σ (PtsOver.map ρ hρ _ y) - 2 * m * c σ = m * (L.φ σ).φ i y + logSq y _ (u i) := fun σ i y hy => by
    have hyt : y ∈ ptsIn p σ (ρ ⁻¹ᵁ ⊤) := mem_ptsIn.2 trivial
    have hgt := gen_mem (mem_ptsIn.1 hyt)
    have hru := hr.unitAt L.isLB (hoff σ y) hy
    have hp := ratVal_pow hru m
    have e₁ : fnOf _ (gen_mem (mem_ptsIn.1 hy)) (u i).val * (r i : X.functionField) ^ m *
        fnOf (ρ ⁻¹ᵁ ⊤) hgt (ρ.app ⊤ b) = fnOf (ρ ⁻¹ᵁ ⊤) hgt (ρ.app ⊤ a) := by
      rw [hu', Units.val_pow_eq_pow_val, div_mul_cancel₀ _ (pow_ne_zero _ (r i).ne_zero), hg]
    have hreg := regAt_fnOf (mem_ptsIn.1 hy) (gen_mem (mem_ptsIn.1 hy)) (u i).val
    have e₂ := congrArg (ratVal · y) e₁
    beta_reduce at e₂
    rw [ratVal_mul (hreg.mul hp.1.regAt) (regAt_fnOf (mem_ptsIn.1 hyt) _ _), ratVal_mul hreg hp.1.regAt, hp.2,
      ratVal_fnOf hy, ratVal_fnOf hyt, ratVal_fnOf hyt, ev_app ρ hρ, ev_app ρ hρ] at e₂
    have e₃ := logNorm_eq (L.φ σ) hr (hoff σ y) hy
    rw [hc] at e₃
    have n₁ := norm_ne_zero_iff.2 (ev_ne_zero hy (u i).isUnit)
    have n₂ := norm_ne_zero_iff.2 (ratVal_ne_zero hru)
    have n₃ := norm_ne_zero_iff.2 (hb σ (PtsOver.map ρ hρ _ y))
    simp only [A, logSq, ← e₂, norm_mul, norm_pow, Real.log_pow,
      Real.log_mul (mul_ne_zero n₁ (pow_ne_zero m n₂)) n₃, Real.log_mul n₁ (pow_ne_zero m n₂), e₃]
    push_cast
    ring
  have hcj : ∀ σ (y : CxPts p σ), m * c ((starRingEnd ℂ).comp σ) = m * c σ := fun σ y => by
    have hy := mem_pick L.isLB y
    have e₁ := key σ _ y hy
    have e₂ := key _ _ (cj y) (cj_mem hy)
    rw [hA σ _ (PtsOver.map ρ hρ _ y) _ (Category.assoc _ _ _), L.conj σ _ _ y (cj y) rfl hy, logSq,
      ev_conj (y := y) rfl hy, RCLike.norm_conj] at e₂
    rw [logSq] at e₁
    linarith
  have hcc : ∀ σ : k →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := fun σ =>
    RingHom.ext fun x => Complex.conj_conj _
  refine ⟨fnB (fun σ z => A σ z + -(m * c σ + m * c ((starRingEnd ℂ).comp σ)))
    (fun σ z => ((cInfAt_log_normSq a (ha σ z)).add (cInfAt_log_normSq b (hb σ z)).neg).add (cInfAt_const _ _))
    fun σ σ' _ z z' h _ => ?_, ?_⟩
  · change A σ' z' + _ = A σ z + _
    rw [hA σ σ' z z' h, eq_conj_of_conj h, hcc, add_comm (m * c σ)]
  · refine isometric_of_local L.B.U (exists_chart L.isLB) (fun _ _ => PUnit.unit) (fun i _ => i)
      (fun _ _ _ => mem_pull.2 trivial) (fun _ _ h => Set.mem_iInter.2 fun _ => h) u (fun x i j hi hj => ?_)
      fun σ i y hy => ?_
    · have e₁ := (gm_pull_g (LB.triv Y) ρ (𝟙 X) x (fun _ => PUnit.unit) (fun _ => PUnit.unit)
        (mem_pull.2 trivial) (mem_pull.2 trivial)).trans (map_one _)
      have e₂ := (gm_linComb L.B (fun _ : PUnit => 𝟙 X) (fun _ => (m : ℤ)) (𝟙 X) x (fun _ => i) (fun _ => j)
        (Set.mem_iInter.2 fun _ => hi) (Set.mem_iInter.2 fun _ => hj)).trans
        ((Fintype.prod_unique _).trans (zpow_natCast _ _))
      refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun s t => s * t⁻¹) e₁ e₂)).symm
      change _ = 1 * (gm (𝟙 X) x _ (L.B.g i j) ^ m)⁻¹ * _
      rw [one_mul, eq_inv_mul_iff_mul_eq]
      refine gm_ext (Units.ext ?_)
      have hij : x ∈ L.B.U i ⊓ L.B.U j := ⟨hi, hj⟩
      rw [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, val_map_gm hij, val_map_gm hi, val_map_gm hj,
        hu', hu', Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hr i j (gen_mem hij)]
      have h0 : fnOf _ (gen_mem hij) (L.B.g i j).val ≠ 0 := ((L.B.g i j).isUnit.map _).ne_zero
      rw [mul_pow, mul_div_assoc', mul_div_mul_left _ _ (pow_ne_zero m h0)]
    · refine (Weight.pull_φ _ ρ hρ _ y).trans (Eq.trans ?_ (congrArg (· + _) ((L.φ σ).zpow_φ m _ y)).symm)
      change A σ _ + _ = _
      have e₁ := key σ i y hy
      rw [hcj σ y]
      push_cast
      linarith

end General

theorem exists_isometric_pull_toSpec : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp (𝓞 F)) (e : ℕ),
    IsArithVar p e → IsArithVar (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) 0 →
    ∀ (L : HermLB p) (r : L.B.ι → X.functionFieldˣ) (hr : GlobalTheory.Cartier.IsRatSec L.B r),
    (∀ (σ : 𝓞 F →+* ℂ) (y : CxPts p σ), y ∈ GlobalTheory.Cartier.offSupp p σ (L.div hr)) →
    (∀ σ, ∃ a : ℝ, ∀ y : CxPts p σ, GlobalTheory.Cartier.logNorm (L.φ σ) r y = a) →
    ∀ (m : ℕ) (g : X.functionFieldˣ) (a b : Γ(X, ⊤)), b ≠ 0 →
      (g : X.functionField) * algebraMap Γ(X, ⊤) X.functionField b = algebraMap Γ(X, ⊤) X.functionField a →
      m • L.div hr = GlobalTheory.Cartier.CartierDiv.principal g →
    ∀ (hρ : (X.toSpecΓ : X ⟶ Sp Γ(X, ⊤)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤) = p),
      ∃ M : HermLB (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)), (L.pow m).Isometric (M.pull X.toSpecΓ hρ) := by
  intro F _ _ X _ _ p e _ hq L r hr hoff hc m g a b hb hg hd hρ
  have inj : Function.Injective (algebraMap Γ(X, ⊤) X.functionField) := X.germToFunctionField_injective ⊤
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hg
    exact mul_ne_zero g.ne_zero ((map_ne_zero_iff _ inj).2 hb) hg
  have hne : ∀ (s : Γ(X, ⊤)), s ≠ 0 → ∀ σ (z : CxPts (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) σ),
      CxPts.ev _ σ ⊤ ((Scheme.ΓSpecIso Γ(X, ⊤)).inv s) z ≠ 0 := fun s hs σ z => by
    refine (mem_ptsIn_basicOpen mem_ptsIn_top _).1 (mem_ptsIn.2 ?_)
    have h₁ := hq.under_eq_genericPoint z
    change under z ∈ _
    rw [h₁]
    refine gen_mem (x := (⊥ : PrimeSpectrum Γ(X, ⊤))) ?_
    erw [basicOpen_eq_of_affine]
    exact hs
  have hpull : ∀ s : Γ(X, ⊤), (X.toSpecΓ.app ⊤) ((Scheme.ΓSpecIso Γ(X, ⊤)).inv s) = s := fun s => by
    have e := Scheme.toSpecΓ_appTop X
    change X.toSpecΓ.appTop _ = s
    rw [e]
    exact (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id_apply s
  refine exists_isometric_pull _ hρ L r hr hoff hc m g _ _ (hne a ha) (hne b hb) (fun h => ?_) hd
  erw [hpull, hpull]
  exact hg

end GlobalTheory.SteinIso

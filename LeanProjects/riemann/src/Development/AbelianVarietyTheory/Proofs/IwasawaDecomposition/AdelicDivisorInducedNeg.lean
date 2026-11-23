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

namespace GlobalTheory.CombInd.DualComb

theorem inv_pow_mul_inv_eq {G : Type} [CommGroup G] (a b c : G) (m : ℕ) :
    b⁻¹ ^ m * c⁻¹ = (a⁻¹ ^ m * c * (a * b) ^ m)⁻¹ := by
  rw [mul_pow, inv_pow, inv_pow, mul_comm (a ^ m)⁻¹ c, mul_assoc, inv_mul_cancel_left, mul_inv_rev]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

variable (Dw) in

theorem expo_neg (w : Sym E →₀ ℤ) : expo Dw (-w) = -expo Dw w := by
  rw [eq_neg_iff_add_eq_zero, ← LineTest.expo_add, neg_add_cancel, LineTest.expo_zero]

theorem parOf_neg (w : Sym E →₀ ℤ) : parOf (-w) = parOf w := by
  simp only [parOf, Finsupp.support_neg]

theorem divOf_neg (n : Letter Dw → ℤ) : divOf Y (-n) = -divOf Y n := by
  simp only [divOf, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

variable {σ : F →+* ℂ} (G : EigMet Z (embOf e σ))

theorem met_neg_h (n : Letter Dw → ℤ) {p : Y.Y.pts σ} {g : Y.Y.Fnˣ} (hg : p ∈ Var.eqnSet σ (divOf Y n) g) :
    (Y.met G (-n)).h g⁻¹ p * (Y.met G n).h g p = 1 := by
  have h' : p ∈ Var.eqnSet σ (divOf Y (-n)) g⁻¹ := by
    show (divOf Y (-n)).IsEqn _ _
    rw [divOf_neg]
    exact CartierDiv.IsEqn.neg hg
  have h := FlagCpt.met_add_h G (-n) n h' hg
  rw [neg_add_cancel, inv_mul_cancel] at h
  rw [← h]
  simp [FlagCpt.met, FlagCpt.genSq, prodPow, Var.tv, Var.hasVal_one.val_eq]

theorem unitAt_eqn_mul (w : Sym E →₀ ℤ) (b : Y.Y.X) :
    UnitAt b ((eqn (divOf Y (expo Dw w)) b * eqn (divOf Y (expo Dw (-w))) b : Y.Y.Fnˣ) : Y.Y.Fn) := by
  have h0 : (divOf Y (expo Dw w) + divOf Y (expo Dw (-w))).IsEqn b
      (eqn (divOf Y (expo Dw w)) b * eqn (divOf Y (expo Dw (-w))) b) :=
    (Base.isEqn_eqn _ b).add (Base.isEqn_eqn _ b)
  rw [← LineTest.divOf_add, ← LineTest.expo_add, add_neg_cancel, LineTest.expo_zero] at h0
  have h00 : (0 : Y.Y.Dv).IsEqn b (eqn (divOf Y (expo Dw w)) b * eqn (divOf Y (expo Dw (-w))) b) := by
    simpa [divOf] using h0
  simpa using (CartierDiv.isEqn_zero b).iff_unitAt.1 h00

open Classical in

theorem lgOf_neg (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) :
    lgOf Y (-w) v ε y = -lgOf Y w v ε y - Real.log (ε.w (valAt y.1
      ((eqn (divOf Y (expo Dw w)) (below y.1) * eqn (divOf Y (expo Dw (-w))) (below y.1) : Y.Y.Fnˣ) : Y.Y.Fn))) := by
  have hp := LineTest.residueCharacteristic_prime v
  have key : ∀ K : Sym E → ℝ, ((-w).sum fun a n => (n : ℝ) * K a) = -(w.sum fun a n => (n : ℝ) * K a) := fun K => by
    rw [Finsupp.sum_neg_index (fun _ => by simp)]
    simp [Finsupp.sum, Finset.sum_neg_distrib]
  unfold lgOf
  rw [dif_pos hp, dif_pos hp]
  dsimp only
  rw [key]
  set b := below y.1 with hb
  set t := (Y.gr_spec b).choose_spec.choose_spec.choose with ht
  set P := ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x with hP
  have hP' : ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (-w) x = P⁻¹ := by
    rw [expo_neg, hP]
    simp only [Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  set e1 := eqn (divOf Y (expo Dw w)) b with he1
  set e2 := eqn (divOf Y (expo Dw (-w))) b with he2
  have hu1 : UnitAt b ((P * e1⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := (Base.isEqn_eqn (divOf Y (expo Dw w)) b).iff_unitAt.1 (LineTest.isEqn_divOf Y (expo Dw w) b)
    rwa [← Units.val_div_eq_div_val, div_eq_mul_inv] at this
  have hu2 : UnitAt b ((P⁻¹ * e2⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := (Base.isEqn_eqn (divOf Y (expo Dw (-w))) b).iff_unitAt.1 (LineTest.isEqn_divOf Y (expo Dw (-w)) b)
    rwa [← Units.val_div_eq_div_val, div_eq_mul_inv, hP'] at this
  have hu : UnitAt b ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn) := unitAt_eqn_mul Y w b
  have hprod : ((P * e1⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) * ((P⁻¹ * e2⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) =
      (((e1 * e2)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    rw [← Units.val_mul, mul_mul_mul_comm, mul_inv_cancel, one_mul, mul_inv]
  have hv1 := (Base.valAt_zpow y.1 hu1).1
  have hv2 := (Base.valAt_zpow y.1 hu2).1
  have hvals : valAt y.1 ((P * e1⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) * valAt y.1 ((P⁻¹ * e2⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) =
      (valAt y.1 ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn))⁻¹ := by
    rw [← OfModel.valAt_mul y.1 hu1.regAt hu2.regAt, hprod, Units.val_inv_eq_inv_val,
      GlobalTheory.LineNorm.Neg.valAt_inv hu]
  have hlog : Real.log (ε.w (valAt y.1 ((P * e1⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      Real.log (ε.w (valAt y.1 ((P⁻¹ * e2⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) =
      -Real.log (ε.w (valAt y.1 ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn))) := by
    rw [← Real.log_mul (ε.w.pos hv1).ne' (ε.w.pos hv2).ne', ← map_mul, hvals, map_inv₀, Real.log_inv]
  rw [hP']
  linear_combination hlog

theorem lg_neg_step (w : Sym E →₀ ℤ) (m : ℕ+) {Lp : LB Y.Y.X} {r : Lp.ι → Y.Y.Fnˣ}
    (hr : Presents ((m : ℕ) • divOf Y (expo Dw w)) Lp r) {i : Lp.ι} {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (y : AlgPt Y.Y) (h₂ : below y.1 ∈ Lp.U i)
    (h1 : ((m : ℕ) : ℝ) * lgOf Y w v ε y = Real.log (ε.w (valAt y.1
      (((eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Y.Fnˣ) : Y.Y.Fn))) -
        ((m : ℕ) : ℝ) * (((1 : ℕ+) : ℕ) : ℝ) * (0 : HeightOneSpectrum (𝓞 F) → ℝ) v) :
    ((m : ℕ) : ℝ) * lgOf Y (-w) v ε y = Real.log (ε.w (valAt y.1
      (((eqn (divOf Y (expo Dw (-w))) (below y.1))⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) -
        ((m : ℕ) : ℝ) * (((1 : ℕ+) : ℕ) : ℝ) * (0 : HeightOneSpectrum (𝓞 F) → ℝ) v := by
  simp only [Pi.zero_apply, mul_zero, sub_zero] at h1 ⊢
  set b := below y.1 with hb
  set e1 := eqn (divOf Y (expo Dw w)) b with he1
  set e2 := eqn (divOf Y (expo Dw (-w))) b with he2
  have hX : UnitAt b ((e1⁻¹ ^ (m : ℕ) * r i : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := ((Base.isEqn_eqn (divOf Y (expo Dw w)) b).nsmul (m : ℕ)).iff_unitAt.1 (hr.isEqn _ _ h₂)
    rwa [← Units.val_div_eq_div_val, div_eq_inv_mul, ← inv_pow] at this
  have hU : UnitAt b ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn) := unitAt_eqn_mul Y w b
  have hXU : UnitAt b ((e1⁻¹ ^ (m : ℕ) * r i * (e1 * e2) ^ (m : ℕ) : Y.Y.Fnˣ) : Y.Y.Fn) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    exact hX.mul (InducedPow.unitAt_pow hU _)
  have hprod : (e2⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Y.Fnˣ) = (e1⁻¹ ^ (m : ℕ) * r i * (e1 * e2) ^ (m : ℕ))⁻¹ :=
    inv_pow_mul_inv_eq e1 e2 (r i) (m : ℕ)
  have hv1 := (Base.valAt_zpow y.1 hX).1
  have hv2 := (Base.valAt_zpow y.1 hU).1
  have hval : valAt y.1 ((e2⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) =
      (valAt y.1 ((e1⁻¹ ^ (m : ℕ) * r i : Y.Y.Fnˣ) : Y.Y.Fn) *
        valAt y.1 ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn) ^ (m : ℕ))⁻¹ := by
    rw [hprod, Units.val_inv_eq_inv_val, GlobalTheory.LineNorm.Neg.valAt_inv hXU, Units.val_mul, Units.val_pow_eq_pow_val,
      OfModel.valAt_mul _ hX.regAt (InducedPow.unitAt_pow hU _).regAt, InducedPow.valAt_pow _ hU.regAt]
  rw [hval, map_inv₀, map_mul, map_pow, Real.log_inv, Real.log_mul (ε.w.pos hv1).ne'
    (pow_ne_zero _ (ε.w.pos hv2).ne'), Real.log_pow, lgOf_neg]
  linear_combination -h1

theorem pn_neg_step {σ : F →+* ℂ} (G G' : EigMet Z (embOf e σ)) (hG : G = G') (n n' : Letter Dw → ℤ) (hn : n' = -n)
    (m : ℕ+) {Lp : LB Y.Y.X} {r : Lp.ι → Y.Y.Fnˣ} (hr : Presents ((m : ℕ) • divOf Y n) Lp r) {i : Lp.ι}
    (y : Pts Y.Y σ) (hi : under y ∈ Lp.U i) (φ₀ : ℝ)
    (hinf : ∀ f : Y.Y.Fn, ((m : ℕ) • divOf Y n).RegularAt (under y) f →
      Real.exp (-(2 * ((m : ℕ) : ℝ) * (((1 : ℕ+) : ℕ) : ℝ) * (0 : InfinitePlace F → ℝ) (InfinitePlace.mk σ))) *
        Var.pn Y.Y σ _ (Var.mPow Y.Y σ _ (m : ℕ) (Y.met G n)) (Var.cx Y.Y σ f) y =
          ‖ratVal (f * (r i : Y.Y.Fn)) y‖ ^ 2 * Real.exp (-φ₀))
    (f : Y.Y.Fn) (hf : ((m : ℕ) • divOf Y n').RegularAt (under y) f) :
    Real.exp (-(2 * ((m : ℕ) : ℝ) * (((1 : ℕ+) : ℕ) : ℝ) * (0 : InfinitePlace F → ℝ) (InfinitePlace.mk σ))) *
      Var.pn Y.Y σ _ (Var.mPow Y.Y σ _ (m : ℕ) (Y.met G' n')) (Var.cx Y.Y σ f) y =
        ‖ratVal (f * (((r i)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn)) y‖ ^ 2 * Real.exp (-(-φ₀)) := by
  subst hG hn
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul] at hinf ⊢
  set g := eqn (divOf Y n) (under y) with hgdef
  have hg : (divOf Y n).IsEqn (under y) g := Base.isEqn_eqn _ _
  have hgm := hg.nsmul (m : ℕ)
  have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 hgm
  have h1 := hinf _ hgen.regularAt
  rw [← Units.val_inv_eq_inv_val, Var.pn_frame (show y ∈ Var.eqnSet σ _ (g ^ (m : ℕ)) from hgm),
    Var.mPow_h (show y ∈ Var.eqnSet σ _ g from hg), ← Units.val_mul] at h1
  have hu : UnitAt (under y) (((g ^ (m : ℕ))⁻¹ * r i : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := hgm.iff_unitAt.1 (hr.isEqn i _ hi)
    rwa [← Units.val_div_eq_div_val, div_eq_inv_mul] at this
  have hgn : (divOf Y (-n)).IsEqn (under y) g⁻¹ := by rw [divOf_neg]; exact hg.neg
  have hg' := hgn.nsmul (m : ℕ)
  rw [Var.pn_eq (show y ∈ Var.eqnSet σ _ (g⁻¹ ^ (m : ℕ)) from hg'),
    Var.mPow_h (show y ∈ Var.eqnSet σ _ g⁻¹ from hgn), Var.fval_cx]
  have hN := met_neg_h Y G n (show y ∈ Var.eqnSet σ _ g from hg)
  have hinvh : (Y.met G (-n)).h g⁻¹ y = ((Y.met G n).h g y)⁻¹ := eq_inv_of_mul_eq_one_left hN
  rw [hinvh, inv_pow ((Y.met G n).h g y) (m : ℕ), h1]
  have hf' : RegAt (under y) (f * ((g⁻¹ ^ (m : ℕ) : Y.Y.Fnˣ) : Y.Y.Fn)) := hg'.regularAt_iff.1 hf
  have hU : ((r i)⁻¹ : Y.Y.Fnˣ) = g⁻¹ ^ (m : ℕ) * ((g ^ (m : ℕ))⁻¹ * r i)⁻¹ := by
    rw [inv_pow, mul_inv_rev, inv_inv, mul_comm (r i)⁻¹, inv_mul_cancel_left]
  have hsplit : f * (((r i)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) =
      f * ((g⁻¹ ^ (m : ℕ) : Y.Y.Fnˣ) : Y.Y.Fn) * (((g ^ (m : ℕ))⁻¹ * r i : Y.Y.Fnˣ) : Y.Y.Fn)⁻¹ := by
    rw [hU, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]
  have hinvr : ratVal ((((g ^ (m : ℕ))⁻¹ * r i : Y.Y.Fnˣ) : Y.Y.Fn))⁻¹ y =
      (ratVal (((g ^ (m : ℕ))⁻¹ * r i : Y.Y.Fnˣ) : Y.Y.Fn) y)⁻¹ := by
    have := ratVal_mul hu.regAt hu.inv.regAt (y := y)
    rw [mul_inv_cancel₀ (Units.ne_zero _), Base.ratVal_one] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  rw [hsplit, ratVal_mul hf' hu.inv.regAt, hinvr, norm_mul, norm_inv, mul_pow, inv_pow, mul_inv, neg_neg,
    Real.exp_neg, inv_inv]
  ring

end Free

theorem induced_neg : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (m : ℕ+) (R : ℝ) (w : Sym D.host.E →₀ ℤ) (L : GlobalTheory.HermLB M.p), (∀ a ∈ w.support, a.2.1 = some R) → (adlOf (Φ.C k) (metsOf x Φ k) w).Induced M L m 0 → (adlOf (Φ.C k) (metsOf x Φ k) (-w)).Induced M L.dual m 0 := by
  intro D A N j S κ s x Φ k M m R w L _ hL
  obtain ⟨hfin, r, hr, hinf, hv⟩ := hL
  unfold Adl.Induced
  refine ⟨hfin, fun i => (r i)⁻¹, ?_, ?_, ?_⟩
  · show Presents ((m : ℕ) • divOf (Φ.C k) (expo S.Dw (-w))) _ _
    rw [expo_neg, divOf_neg, smul_neg]
    exact GlobalTheory.LineNorm.Neg.presents_neg L.isLB M.j hr
  · intro σ y y' i f hy hi hf
    exact pn_neg_step (Φ.C k) (x.eigMetAt (embOf κ.e σ) (parOf w)) (x.eigMetAt (embOf κ.e σ) (parOf (-w)))
      (by rw [parOf_neg]) (expo S.Dw w) (expo S.Dw (-w)) (expo_neg S.Dw w) m hr y hi
      ((L.φ _).φ (i PUnit.unit) y') (fun f hf => hinf σ y y' i f hy hi hf) f hf
  · intro v ε y yt i h hi
    exact lg_neg_step (Φ.C k) w m hr ε y (OfModel.le_chart M L.B ε y yt h (i := i) hi trivial) (hv v ε y yt i h hi)

end GlobalTheory.CombInd.DualComb

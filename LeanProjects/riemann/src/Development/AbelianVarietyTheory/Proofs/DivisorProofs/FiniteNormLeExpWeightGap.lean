import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSymEqSingle
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CovHt.Link.FrameLog

theorem zpow_neg_mul_pow {G : Type} [Group G] (a : G) (t U : ℤ) (K : ℕ) : a ^ (-(t * K * U)) = (a ^ (-(t * U))) ^ K := by
  rw [← zpow_natCast, ← zpow_mul, mul_right_comm, neg_mul]

section Units

variable {X : AlgebraicGeometry.Scheme.{0}} [AlgebraicGeometry.IsIntegral X] {x : X}

theorem unitAt_zpow {u : X.functionFieldˣ} (hu : UnitAt x (u : X.functionField)) (n : ℤ) :
    UnitAt x ((u ^ n : X.functionFieldˣ) : X.functionField) := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    exact ApproxSec.unitAt_pow hu n
  · rw [zpow_negSucc, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    exact (ApproxSec.unitAt_pow hu _).inv

theorem unitAt_prod {ι : Type} (s : Finset ι) (u : ι → X.functionFieldˣ) (hu : ∀ i ∈ s, UnitAt x (u i : X.functionField)) :
    UnitAt x ((∏ i ∈ s, u i : X.functionFieldˣ) : X.functionField) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one x
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul]
    exact (hu a (Finset.mem_insert_self a s)).mul (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

end Units

section LogVal

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v) (y : AlgPt Y)

theorem log_valAt_mul' {a b : Y.Fn} (ha : UnitAt (below y.1) a) (hb : UnitAt (below y.1) b) :
    Real.log (ε.w (valAt y.1 (a * b))) = Real.log (ε.w (valAt y.1 a)) + Real.log (ε.w (valAt y.1 b)) := by
  rw [SmallSec.valAt_mul ha.regAt hb.regAt, map_mul,
    Real.log_mul (ε.w.pos (SmallSec.valAt_ne_zero ha)).ne' (ε.w.pos (SmallSec.valAt_ne_zero hb)).ne']

theorem log_valAt_one : Real.log (ε.w (valAt y.1 (1 : Y.Fn))) = 0 := by
  have h := log_valAt_mul' ε y (unitAt_one (below y.1)) (unitAt_one (below y.1))
  rw [mul_one] at h
  linarith

theorem log_valAt_zpow {u : Y.Fnˣ} (hu : UnitAt (below y.1) (u : Y.Fn)) (n : ℤ) :
    Real.log (ε.w (valAt y.1 ((u ^ n : Y.Fnˣ) : Y.Fn))) = n * Real.log (ε.w (valAt y.1 (u : Y.Fn))) := by
  have hnat (m : ℕ) : Real.log (ε.w (valAt y.1 ((u ^ m : Y.Fnˣ) : Y.Fn))) = m * Real.log (ε.w (valAt y.1 (u : Y.Fn))) := by
    rw [Units.val_pow_eq_pow_val, SmallSec.valAt_pow hu.regAt, map_pow, Real.log_pow]
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, hnat]; simp
  · have h1 := log_valAt_mul' ε y (unitAt_zpow hu (Int.negSucc n)) (unitAt_zpow hu ((n + 1 : ℕ) : ℤ))
    rw [← Units.val_mul, ← zpow_add, show Int.negSucc n + ((n + 1 : ℕ) : ℤ) = 0 by simp [Int.negSucc_eq], zpow_zero,
      Units.val_one, log_valAt_one, zpow_natCast, hnat] at h1
    rw [Int.cast_negSucc]
    linarith

theorem log_valAt_prod {ι : Type} (s : Finset ι) (u : ι → Y.Fnˣ) (hu : ∀ i ∈ s, UnitAt (below y.1) (u i : Y.Fn)) :
    Real.log (ε.w (valAt y.1 ((∏ i ∈ s, u i : Y.Fnˣ) : Y.Fn))) = ∑ i ∈ s, Real.log (ε.w (valAt y.1 (u i : Y.Fn))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using log_valAt_one ε y
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Units.val_mul,
      log_valAt_mul' ε y (hu a (Finset.mem_insert_self a s)) (unitAt_prod s u fun i hi => hu i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hu i (Finset.mem_insert_of_mem hi)]

end LogVal

section FreeSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem frT_zsmul (a : ℤ) (n : Letter Dw → ℤ) (b : Y.Y.X) : frT Y (a • n) b = frT Y n b ^ a := by
  rw [frT, frT, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun x _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]

theorem frT_sum {ι : Type} (s : Finset ι) (a : ι → ℤ) (n : ι → Letter Dw → ℤ) (b : Y.Y.X) :
    frT Y (∑ i ∈ s, a i • n i) b = ∏ i ∈ s, frT Y (n i) b ^ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frT]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, frT_add, ih, frT_zsmul]

variable (Dw) in

theorem expo_sum {ι : Type} (s : Finset ι) (a : ι → ℤ) (w : ι → Sym E →₀ ℤ) :
    expo Dw (∑ i ∈ s, a i • w i) = ∑ i ∈ s, a i • expo Dw (w i) := by
  let φ : (Sym E →₀ ℤ) →+ (Letter Dw → ℤ) :=
    AddMonoidHom.mk' (expo Dw) (LineTest.expo_add Dw)
  have := map_sum φ (fun i => a i • w i) s
  simp only [map_zsmul] at this
  exact this

end FreeSum

section RealKey

theorem real_root {p a b V r : ℝ} {nM nQ q τ rn : ℕ} (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hV : 0 < V)
    (hM : 0 < nM) (hQ : 0 < nQ) (hq : 0 < q) (hr : r * q = rn)
    (h : p ^ (nM * (nQ * q)) = a ^ (nQ * q) * b ^ (nM * τ * rn) * V) :
    p = a ^ (1 / (nM : ℝ)) * (b ^ (1 / (nQ : ℝ))) ^ ((τ : ℝ) * r) * Real.exp (Real.log V / ((nM * (nQ * q) : ℕ) : ℝ)) := by
  have hK : nM * (nQ * q) ≠ 0 := by positivity
  have hM' : (nM : ℝ) ≠ 0 := by positivity
  have hQ' : (nQ : ℝ) ≠ 0 := by positivity
  have hK' : ((nM * (nQ * q) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  refine (pow_left_inj₀ hp (by positivity) hK).1 ?_
  have e1 : (a ^ (1 / (nM : ℝ))) ^ (nM * (nQ * q)) = a ^ (nQ * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha, ← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
  have e2 : ((b ^ (1 / (nQ : ℝ))) ^ ((τ : ℝ) * r)) ^ (nM * (nQ * q)) = b ^ (nM * τ * rn) := by
    rw [← Real.rpow_mul hb, ← Real.rpow_natCast, ← Real.rpow_mul hb, ← Real.rpow_natCast]
    congr 1
    push_cast
    rw [← hr]
    field_simp
  have e3 : Real.exp (Real.log V / ((nM * (nQ * q) : ℕ) : ℝ)) ^ (nM * (nQ * q)) = V := by
    rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hK', Real.exp_log hV]
  rw [h, mul_pow, mul_pow, e1, e2, e3]

theorem real_expo {ι : Type} [Fintype ι] (l LH LR U d cM cQ : ι → ℝ) (g r τ nM nQ nab K cM0 cQ0 : ℝ)
    (hM : nM ≠ 0) (hQ : nQ ≠ 0) (hab : nab ≠ 0) (hK : K ≠ 0) (hM0 : cM0 * nab = nM * r) (hQ0 : cQ0 * nab = -nQ)
    (hMx : ∀ x, cM x = nM * (-(U x - r * d x))) (hQx : ∀ x, cQ x = nQ * (-d x)) :
    (∑ x, (-(τ * K * U x)) * l x) / K + ∑ x, (-(τ * U x)) * LR x =
      τ * (cM0 * g + ∑ x, cM x * (l x + LH x)) / nM + 1 * (cQ0 * g + ∑ x, cQ x * (l x + LR x)) / nQ * (τ * r) +
        τ * ∑ x, (-(U x - r * d x)) * (LR x - LH x) := by
  have a1 : cM0 = nM * r / nab := by field_simp; linarith
  have a2 : cQ0 = -nQ / nab := by field_simp; linarith
  have b1 : (∑ x, (-(τ * K * U x)) * l x) / K = ∑ x, (-(τ * U x)) * l x := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun x _ => by field_simp
  have b2 : τ * (cM0 * g + ∑ x, cM x * (l x + LH x)) / nM =
      τ * r / nab * g + ∑ x, τ * (-(U x - r * d x)) * (l x + LH x) := by
    rw [mul_add, add_div, Finset.mul_sum, Finset.sum_div, a1]
    congr 1
    · field_simp
    · exact Finset.sum_congr rfl fun x _ => by rw [hMx]; field_simp
  have b3 : 1 * (cQ0 * g + ∑ x, cQ x * (l x + LR x)) / nQ * (τ * r) =
      -(τ * r / nab * g) + ∑ x, τ * r * (-d x) * (l x + LR x) := by
    rw [one_mul, add_div, add_mul, Finset.sum_div, Finset.sum_mul, a2]
    congr 1
    · field_simp
    · exact Finset.sum_congr rfl fun x _ => by rw [hQx]; field_simp
  rw [b1, b2, b3, Finset.mul_sum, ← Finset.sum_add_distrib]
  have : ∑ x, (-(τ * U x) * l x + -(τ * U x) * LR x) = ∑ x, (τ * (-(U x - r * d x)) * (l x + LH x) +
      τ * r * (-d x) * (l x + LR x) + τ * (-(U x - r * d x) * (LR x - LH x))) :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end RealKey

section ValKey

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v) (y : AlgPt Y)

theorem val_root (hx : IsIntegrallyClosed (Y.X.presheaf.stalk (below y.1))) (f : Y.Fn) (T EM EQ V : Y.Fnˣ) {r : ℝ}
    {nM nQ q τ rn : ℕ} (hM : 0 < nM) (hQ : 0 < nQ) (hq : 0 < q) (hr : r * q = rn)
    (hX : RegAt (below y.1) (f ^ nM * (EM : Y.Fn) ^ τ)) (hY : RegAt (below y.1) (EQ : Y.Fn))
    (hV : UnitAt (below y.1) (V : Y.Fn))
    (h : EM ^ (τ * (nQ * q)) * EQ ^ (nM * τ * rn) * V = T ^ (nM * (nQ * q))) :
    ε.w (valAt y.1 (f * T)) = ε.w (valAt y.1 (f ^ nM * (EM : Y.Fn) ^ τ)) ^ (1 / (nM : ℝ)) *
      (ε.w (valAt y.1 (1 ^ nQ * (EQ : Y.Fn) ^ 1)) ^ (1 / (nQ : ℝ))) ^ ((τ : ℝ) * r) *
      Real.exp (Real.log (ε.w (valAt y.1 (V : Y.Fn))) / ((nM * (nQ * q) : ℕ) : ℝ)) := by
  have key : (f * T) ^ (nM * (nQ * q)) = (f ^ nM * (EM : Y.Fn) ^ τ) ^ (nQ * q) * (EQ : Y.Fn) ^ (nM * τ * rn) * V := by
    have h' := congrArg Units.val h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h'
    rw [mul_pow, ← h', mul_pow, ← pow_mul, ← pow_mul]
    ring
  have h1 := ApproxSec.regAt_pow hX (nQ * q)
  have h2 := ApproxSec.regAt_pow hY (nM * τ * rn)
  have hreg : RegAt (below y.1) (f * T) :=
    ApproxSec.regAt_of_pow hx (Nat.mul_pos hM (Nat.mul_pos hQ hq)) (key ▸ (h1.mul h2).mul hV.regAt)
  rw [one_pow, one_mul, pow_one]
  refine real_root (ε.w.nonneg _) (ε.w.nonneg _) (ε.w.nonneg _) (ε.w.pos (SmallSec.valAt_ne_zero hV)) hM hQ hq hr ?_
  rw [← map_pow, ← SmallSec.valAt_pow hreg, key, SmallSec.valAt_mul (h1.mul h2) hV.regAt, SmallSec.valAt_mul h1 h2,
    SmallSec.valAt_pow hX, SmallSec.valAt_pow hY, map_mul, map_mul, map_pow, map_pow]

end ValKey

section Core

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

set_option maxHeartbeats 2000000 in

theorem finN_eq_core (ab : Adl (cxSt D.what₂.LL) (Φ.C k).Y) (wH wR : DV.Rt D.what₂.Tau N → (Sym D.host.E →₀ ℤ))
    (hH : ∀ x, expo S.Dw (wH x) = rootExp S x) (hR : ∀ x, expo S.Dw (wR x) = rootExp S x)
    (mH mR : Mets (Φ.C k) (cxSt D.what₂.LL)) (la : AllWt.Weight S.Dw) (τ : ℕ) (U : DV.Rt D.what₂.Tau N → ℤ)
    (hla : drSym la = ∑ x, (-((τ : ℤ) * U x)) • wR x) (d : DV.Rt D.what₂.Tau N → ℚ) {r : ℚ} (hr : 0 < r)
    (ρM ρQ : Option (DV.Rt D.what₂.Tau N) → Adl (cxSt D.what₂.LL) (Φ.C k).Y) (tM tQ : Option (DV.Rt D.what₂.Tau N) → ℚ)
    (gM gQ : ∀ σ, Pts (Φ.C k).Y σ → ℝ)
    (hρM0 : ρM none = ab) (hρMx : ∀ x, ρM (some x) = adlOf (Φ.C k) mH (wH x))
    (hρQ0 : ρQ none = ab) (hρQx : ∀ x, ρQ (some x) = adlOf (Φ.C k) mR (wR x))
    (htM0 : tM none = r) (htMx : ∀ x, tM (some x) = -(U x - r * d x))
    (htQ0 : tQ none = -1) (htQx : ∀ x, tQ (some x) = -d x)
    (hQ : (comb ρQ tQ gQ).D.Eff) (f : (Φ.C k).Y.Fn) (hf : f ∈ (comb ρM tM gM).secs τ)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (Φ.C k).Y) :
    finN Φ k la v e y f = (comb ρM tM gM).nrmFin v τ f e y * (comb ρQ tQ gQ).nrmFin v 1 1 e y ^ ((τ : ℝ) * r) *
      Real.exp (τ * ∑ x, (-((U x : ℝ) - r * d x)) * (lgLin (Φ.C k) (wR x) v e y - lgLin (Φ.C k) (wH x) v e y)) := by
  classical
  rw [nrmFin_comb, nrmFin_comb, finN, lgOf_eq]
  have hcEM : combEqn ρM tM (below y.1) = eqn ab.D (below y.1) ^ combNum ρM tM none *
      ∏ x, eqn (divOf (Φ.C k) (rootExp S x)) (below y.1) ^ combNum ρM tM (some x) := by
    rw [combEqn, Fintype.prod_option, hρM0]
    congr 1
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [hρMx]
    show eqn (divOf (Φ.C k) (expo S.Dw (wH x))) (below y.1) ^ _ = _
    rw [hH]
  have hcEQ : combEqn ρQ tQ (below y.1) = eqn ab.D (below y.1) ^ combNum ρQ tQ none *
      ∏ x, eqn (divOf (Φ.C k) (rootExp S x)) (below y.1) ^ combNum ρQ tQ (some x) := by
    rw [combEqn, Fintype.prod_option, hρQ0]
    congr 1
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [hρQx]
    show eqn (divOf (Φ.C k) (expo S.Dw (wR x))) (below y.1) ^ _ = _
    rw [hR]
  have hTdr : frT (Φ.C k) (expo S.Dw (drSym la)) (below y.1) =
      ∏ x, frT (Φ.C k) (rootExp S x) (below y.1) ^ (-((τ : ℤ) * U x)) := by
    rw [hla, expo_sum, frT_sum]
    simp only [hR]
  have hab : ((ab.n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 ab.n.ne_zero
  have hM0 : (combNum ρM tM none : ℚ) * (ab.n : ℕ) = (combDen ρM tM : ℕ) * r := by
    have := combNum_mul ρM tM none
    rwa [hρM0, htM0] at this
  have hQ0 : (combNum ρQ tQ none : ℚ) * (ab.n : ℕ) = -(combDen ρQ tQ : ℕ) := by
    have := combNum_mul ρQ tQ none
    rw [hρQ0, htQ0] at this
    linarith
  have hMx (x : DV.Rt D.what₂.Tau N) : (combNum ρM tM (some x) : ℚ) = (combDen ρM tM : ℕ) * (-(U x - r * d x)) := by
    have := combNum_mul ρM tM (some x)
    rw [hρMx, htMx] at this
    simpa [adlOf] using this
  have hQx (x : DV.Rt D.what₂.Tau N) : (combNum ρQ tQ (some x) : ℚ) = (combDen ρQ tQ : ℕ) * (-d x) := by
    have := combNum_mul ρQ tQ (some x)
    rw [hρQx, htQx] at this
    simpa [adlOf] using this
  obtain ⟨rn, hrn⟩ : ∃ rn : ℕ, (rn : ℤ) = r.num := ⟨r.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.2 hr.le)⟩
  have hrq : r * r.den = rn := by
    rw [Rat.mul_den_eq_num, ← hrn, Int.cast_natCast]
  have hgrp : combEqn ρM tM (below y.1) ^ (τ * ((combDen ρQ tQ : ℕ) * r.den)) *
      combEqn ρQ tQ (below y.1) ^ ((combDen ρM tM : ℕ) * τ * rn) *
      ∏ x, (frT (Φ.C k) (rootExp S x) (below y.1) * (eqn (divOf (Φ.C k) (rootExp S x)) (below y.1))⁻¹) ^
        (-((τ : ℤ) * ((combDen ρM tM : ℕ) * ((combDen ρQ tQ : ℕ) * r.den) : ℕ) * U x)) =
      frT (Φ.C k) (expo S.Dw (drSym la)) (below y.1) ^ ((combDen ρM tM : ℕ) * ((combDen ρQ tQ : ℕ) * r.den)) := by
    rw [hcEM, hcEQ, hTdr, ← Finset.prod_pow]
    refine (grp_key Finset.univ (eqn ab.D (below y.1)) (fun x => eqn (divOf (Φ.C k) (rootExp S x)) (below y.1))
      (fun x => frT (Φ.C k) (rootExp S x) (below y.1)) (combNum ρM tM none) (combNum ρQ tQ none)
      (fun x => combNum ρM tM (some x)) (fun x => combNum ρQ tQ (some x))
      (fun x => -((τ : ℤ) * ((combDen ρM tM : ℕ) * ((combDen ρQ tQ : ℕ) * r.den) : ℕ) * U x))
      (τ * ((combDen ρQ tQ : ℕ) * r.den)) ((combDen ρM tM : ℕ) * τ * rn) ?_ ?_).trans ?_
    · have h : ((combNum ρM tM none * ((τ * ((combDen ρQ tQ : ℕ) * r.den) : ℕ) : ℤ) +
          combNum ρQ tQ none * (((combDen ρM tM : ℕ) * τ * rn : ℕ) : ℤ) : ℤ) : ℚ) * (ab.n : ℕ) = 0 := by
        push_cast
        linear_combination ((τ : ℚ) * ((combDen ρQ tQ : ℕ) * r.den)) * hM0 + (((combDen ρM tM : ℕ) : ℚ) * τ * rn) * hQ0 +
          (τ * ((combDen ρM tM : ℕ) : ℚ) * ((combDen ρQ tQ : ℕ) : ℚ)) * hrq
      exact_mod_cast (mul_eq_zero.1 h).resolve_right hab
    · intro x _
      have h : ((combNum ρM tM (some x) * ((τ * ((combDen ρQ tQ : ℕ) * r.den) : ℕ) : ℤ) +
          combNum ρQ tQ (some x) * (((combDen ρM tM : ℕ) * τ * rn : ℕ) : ℤ) : ℤ) : ℚ) =
          ((-((τ : ℤ) * ((combDen ρM tM : ℕ) * ((combDen ρQ tQ : ℕ) * r.den) : ℕ) * U x) : ℤ) : ℚ) := by
        push_cast
        rw [hMx, hQx]
        linear_combination ((τ : ℚ) * ((combDen ρM tM : ℕ) : ℚ) * ((combDen ρQ tQ : ℕ) : ℚ) * d x) * hrq
      exact_mod_cast h
    · refine Finset.prod_congr rfl fun x _ => ?_
      exact zpow_neg_mul_pow _ _ _ _
  have hUx (x : DV.Rt D.what₂.Tau N) := unitAt_frT (Φ.C k) (rootExp S x) (below y.1)
  have hX : RegAt (below y.1) (f ^ (combDen ρM tM : ℕ) * (combEqn ρM tM (below y.1) : (Φ.C k).Y.Fn) ^ τ) := by
    have := ((isEqn_combEqn ρM tM (below y.1)).nsmul τ).regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hf (below y.1))
    rwa [Units.val_pow_eq_pow_val] at this
  have hY : RegAt (below y.1) (combEqn ρQ tQ (below y.1) : (Φ.C k).Y.Fn) :=
    CartierDiv.eff_iff.1 hQ _ _ (isEqn_combEqn ρQ tQ (below y.1))
  have hrq' : (r : ℝ) * (r.den : ℕ) = (rn : ℕ) := by exact_mod_cast hrq
  have hroot := val_root e y (have := (Φ.C k).Y.isNormalScheme; inferInstance) f _ _ _ _ (combDen ρM tM).pos
    (combDen ρQ tQ).pos r.den_pos hrq' hX hY
    (unitAt_prod _ _ fun x _ => unitAt_zpow (hUx x) _) hgrp
  rw [log_valAt_prod e y _ _ fun x _ => unitAt_zpow (hUx x) _] at hroot
  simp only [log_valAt_zpow e y (hUx _)] at hroot
  have hUd := unitAt_frT (Φ.C k) (expo S.Dw (drSym la)) (below y.1)
  have hfT : f * (frT (Φ.C k) (expo S.Dw (drSym la)) (below y.1) : (Φ.C k).Y.Fn) =
      f * (eqn (divOf (Φ.C k) (expo S.Dw (drSym la))) (below y.1) : (Φ.C k).Y.Fn) *
        ((frT (Φ.C k) (expo S.Dw (drSym la)) (below y.1) *
          (eqn (divOf (Φ.C k) (expo S.Dw (drSym la))) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) := by
    rw [mul_assoc, ← Units.val_mul, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hfT, valAt_mul_unit _ hUd, map_mul] at hroot
  rw [Real.exp_add, Real.exp_log (e.w.pos (SmallSec.valAt_ne_zero hUd)), ← mul_assoc, hroot]
  have hlin : lgLin (Φ.C k) (drSym la) v e y = ∑ x, (-((τ : ℝ) * U x)) * lgLin (Φ.C k) (wR x) v e y := by
    rw [hla, lgLin_sum]
    push_cast
    rfl
  have hlgM : ∑ i, (combNum ρM tM i : ℝ) * (ρM i).lg v e y = combNum ρM tM none * ab.lg v e y +
      ∑ x, (combNum ρM tM (some x) : ℝ) * (Real.log (e.w (valAt y.1 ((frT (Φ.C k) (rootExp S x) (below y.1) *
        (eqn (divOf (Φ.C k) (rootExp S x)) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))) +
        lgLin (Φ.C k) (wH x) v e y) := by
    rw [Fintype.sum_option, hρM0]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hρMx, ← hH, ← lgOf_eq]
    rfl
  have hlgQ : ∑ i, (combNum ρQ tQ i : ℝ) * (ρQ i).lg v e y = combNum ρQ tQ none * ab.lg v e y +
      ∑ x, (combNum ρQ tQ (some x) : ℝ) * (Real.log (e.w (valAt y.1 ((frT (Φ.C k) (rootExp S x) (below y.1) *
        (eqn (divOf (Φ.C k) (rootExp S x)) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))) +
        lgLin (Φ.C k) (wR x) v e y) := by
    rw [Fintype.sum_option, hρQ0]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hρQx, ← hR, ← lgOf_eq]
    rfl
  have hex := real_expo (fun x => Real.log (e.w (valAt y.1 ((frT (Φ.C k) (rootExp S x) (below y.1) *
        (eqn (divOf (Φ.C k) (rootExp S x)) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))))
    (fun x => lgLin (Φ.C k) (wH x) v e y) (fun x => lgLin (Φ.C k) (wR x) v e y) (fun x => (U x : ℝ)) (fun x => (d x : ℝ))
    (fun x => (combNum ρM tM (some x) : ℝ)) (fun x => (combNum ρQ tQ (some x) : ℝ)) (ab.lg v e y) r τ
    ((combDen ρM tM : ℕ) : ℝ) ((combDen ρQ tQ : ℕ) : ℝ) ((ab.n : ℕ) : ℝ)
    (((combDen ρM tM : ℕ) * ((combDen ρQ tQ : ℕ) * r.den) : ℕ) : ℝ) (combNum ρM tM none) (combNum ρQ tQ none)
    (Nat.cast_ne_zero.2 (combDen ρM tM).ne_zero) (Nat.cast_ne_zero.2 (combDen ρQ tQ).ne_zero)
    (Nat.cast_ne_zero.2 ab.n.ne_zero)
    (Nat.cast_ne_zero.2 (Nat.mul_pos (combDen ρM tM).pos (Nat.mul_pos (combDen ρQ tQ).pos r.den_pos)).ne')
    (by exact_mod_cast hM0) (by exact_mod_cast hQ0) (fun x => by exact_mod_cast hMx x) (fun x => by exact_mod_cast hQx x)
  rw [hlin, hlgM, hlgQ, Real.mul_rpow (Real.rpow_nonneg (e.w.nonneg _) _) (Real.exp_pos _).le, ← Real.exp_mul,
    mul_assoc, ← Real.exp_add]
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_natCast, Nat.cast_one]
  rw [hex, Real.exp_add, Real.exp_add]
  ring

theorem finN_le : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (r : ℚ), 0 < r → ∀ (k : s.Comp) (τ : ℕ), 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR L u) r k).secs τ, ∀ v e y, finN Φ k (τ • u) v e y f ≤ (mbarOf P B (wtR L u) r k).nrmFin v τ f e y * Real.exp (τ * ∑ z : DV.Rt D.what₂.Tau N, |wtR L u z.1 z.2 - r * P.dir z.1 z.2| * |lgOf (Φ.C k) (rootSym S.Dw (fun _ => false) none (DV.tauEmb D z.1) z.2) v e y - lgOf (Φ.C k) (rootSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D z.1) z.2) v e y|) * (bdQ P k).nrmFin v 1 1 e y ^ ((τ : ℝ) * r) := by
  intro D A N j S κ s Φ L x P B u r hr k τ _ f hf v e y
  have e0 : wtR L u = fun t i => ((u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ) : ℝ) := by
    funext t i; simp [wtR]
  have e1 : mbarOf P B (wtR L u) r k = P.mbarQ k B (fun t i => (u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ)) r := by
    rw [e0, mbarOf_cast P B _ hr]
  rw [e1] at hf ⊢
  have hla : drSym (τ • u) = ∑ z : DV.Rt D.what₂.Tau N, (-((τ : ℤ) * u (L.ψ z.1) (Fin.cast S.rank_eq.symm z.2))) •
      rootSym S.Dw (fun _ => false) none (DV.tauEmb D z.1) z.2 := by
    rw [drSym_eq S L]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp
  have h := finN_eq_core Φ k (P.ab k) (fun z => rootSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D z.1) z.2)
    (fun z => rootSym S.Dw (fun _ => false) none (DV.tauEmb D z.1) z.2) (fun z => expo_rootSym _ _ _ _ _)
    (fun z => expo_rootSym _ _ _ _ _) (fun _ => refMet x Φ k) (fun _ => refMet x Φ k) (τ • u) τ _ hla (fun z => P.dirQ z.1 z.2) hr (P.gens k B) _ _ _ _ _
    rfl (fun _ => rfl) rfl (fun _ => rfl) rfl (fun _ => rfl) rfl (fun _ => rfl) (eff_bdQ P k) f hf v e y
  refine h.trans_le ?_
  rw [mul_right_comm]
  have hn (M : Adl (cxSt D.what₂.LL) (Φ.C k).Y) (t : ℕ) (g : (Φ.C k).Y.Fn) : 0 ≤ M.nrmFin v t g e y :=
    mul_nonneg (Real.rpow_nonneg (e.w.nonneg _) _) (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun z _ => ?_) (Nat.cast_nonneg _))) (hn _ _ _)) (Real.rpow_nonneg (hn _ _ _) _)
  rw [lgOf_eq, lgOf_eq, expo_rootSym, expo_rootSym, add_sub_add_left_eq_sub, ← abs_mul, ← abs_neg, ← neg_mul]
  exact le_abs_self _

end Core

end GlobalTheory.CovHt.Link.FrameLog

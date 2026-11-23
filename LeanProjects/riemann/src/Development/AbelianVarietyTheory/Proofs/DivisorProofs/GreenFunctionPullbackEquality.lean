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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOnPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExtensionOfPhaseFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionDivDetUnit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ShFam.Pad GlobalTheory.FlatSecCover

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatSecConst

open GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.Toroidal

variable {D : D7} {O : Setup D} (hO : O.Core) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (y : Pts (O.var c) σ)

private theorem exists_isEqn {X : Scheme.{0}} [IsIntegral X] {Δ : CartierDiv X} {x : X} {f : X.functionField}
    (h : Δ.GeneratesAt x f) : ∃ u : X.functionFieldˣ, Δ.IsEqn x u ∧ f = ((u⁻¹ : X.functionFieldˣ) : X.functionField) := by
  have h0 : f ≠ 0 := have ⟨_, _, hu⟩ := h; left_ne_zero_of_mul hu.ne_zero
  exact ⟨(Units.mk0 f h0)⁻¹, CartierDiv.isEqn_iff_generatesAt_inv.2 (by simpa using h), by simp⟩

include hO

private theorem pn_pos (n : Letter O.S.Dw → ℤ) {f : (O.var c).Fn} (hf : (divOf (O.Φ.C c) n).GeneratesAt (under y) f) :
    0 < (cxSt _).pn _ σ _ (O.met.h0 c σ n) ((cxSt _).cx _ σ f) y := by
  obtain ⟨a, ha, e⟩ := exists_pn_eq (C := cxSt D.what₂.LL) hf
  rw [e]
  exact mul_pos ha (hO.referenceMetric_posAt c σ n y)

private theorem lnN_add (n n' : Letter O.S.Dw → ℤ) {f f' : (O.var c).Fn} (hf : (divOf (O.Φ.C c) n).GeneratesAt (under y) f)
    (hf' : (divOf (O.Φ.C c) n').GeneratesAt (under y) f') :
    lnN (O.met.h0 c σ (n + n')) (f * f') y = lnN (O.met.h0 c σ n) f y + lnN (O.met.h0 c σ n') f' y := by
  have p₁ := pn_pos hO c σ y n hf
  have p₂ := pn_pos hO c σ y n' hf'
  have key : (cxSt _).pn _ σ _ (O.met.h0 c σ (n + n')) ((cxSt _).cx _ σ (f * f')) y =
      (cxSt _).pn _ σ _ (O.met.h0 c σ n) ((cxSt _).cx _ σ f) y *
        (cxSt _).pn _ σ _ (O.met.h0 c σ n') ((cxSt _).cx _ σ f') y := by
    obtain ⟨u, hu, rfl⟩ := exists_isEqn hf
    obtain ⟨u', hu', rfl⟩ := exists_isEqn hf'
    obtain ⟨xa, P, hc⟩ := hO
    have huu : (divOf (O.Φ.C c) (n + n')).IsEqn (under y) (u * u') := by
      rw [FlagCpt.divOf_add]
      exact hu.add hu'
    rw [hc.h0_eq, ← Units.val_mul, ← mul_inv]
    exact (Var.pn_frame huu).trans ((FlagCpt.met_add_h (xa.eigMet (embOf O.κ.e σ)) n n' hu hu').trans
      (congrArg₂ (· * ·) (Var.pn_frame hu).symm (Var.pn_frame hu').symm))
  simp only [lnN]
  rw [key, Real.log_mul p₁.ne' p₂.ne', add_div]

private theorem lnN_neg (n : Letter O.S.Dw → ℤ) {f : (O.var c).Fn} (hf : (divOf (O.Φ.C c) n).GeneratesAt (under y) f) :
    lnN (O.met.h0 c σ (-n)) f⁻¹ y = -lnN (O.met.h0 c σ n) f y := by
  simp only [lnN]
  rw [eq_inv_of_mul_eq_one_right (hO.referenceMetric_mul_dual_eq_one c σ n hf), Real.log_inv, neg_div]

private theorem lnN_sum {ι : Type} (s : Finset ι) (n : ι → Letter O.S.Dw → ℤ) (f : ι → (O.var c).Fn)
    (hf : ∀ i, (divOf (O.Φ.C c) (n i)).GeneratesAt (under y) (f i)) :
    lnN (O.met.h0 c σ (∑ i ∈ s, n i)) (∏ i ∈ s, f i) y = ∑ i ∈ s, lnN (O.met.h0 c σ (n i)) (f i) y := by
  induction s using Finset.induction_on with
  | empty =>
    have h1 : (divOf (O.Φ.C c) 0).GeneratesAt (under y) (1 : (O.var c).Fn) := by
      have := generatesAt_prod (∅ : Finset ι) (Δ := fun i => divOf (O.Φ.C c) (n i)) (x := under y) (f := f)
        fun i _ => hf i
      rwa [← GlobalTheory.OmCx.divOf_sum O c] at this
    have h2 := lnN_add hO c σ y 0 0 h1 h1
    rw [add_zero, mul_one] at h2
    rw [Finset.sum_empty, Finset.prod_empty, Finset.sum_empty]
    linarith
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Finset.sum_insert hj, lnN_add hO c σ y _ _ (hf j), ih]
    rw [GlobalTheory.OmCx.divOf_sum O c]
    exact generatesAt_prod s fun i _ => hf i

private theorem rootLn_eq (B : ℝ) (τ : D.what₂.Tau) (i : Fin O.N) :
    rootLn O c B (τ, i) σ y = lnN (O.met.h0 c σ (O.ex (τ, i))) (rootFn O c B (τ, i) (under y)) y := by
  have hp := O.S.p_eq
  have hr := O.S.rank_eq
  have hi' := i.isLt
  have tr : ∀ {n n' : Letter O.S.Dw → ℤ}, n = n' → ∀ f, lnN (O.met.h0 c σ n) f y = lnN (O.met.h0 c σ n') f y := by
    rintro n _ rfl f
    rfl
  have la : ∀ st, lnAdl (lineAdl O c B st) σ y =
      lnN (O.met.h0 c σ (expo O.S.Dw (Finsupp.single (ArIn.ind (FlagAr.setB O.Y B), (none : Option ℝ), st) 1)))
        (genAt (lineAdl O c B st).D (under y)) y := fun st => by
    simp only [lnAdl, lineAdl, Setup.adl0, adlOf, Pi.zero_apply, mul_zero, sub_zero]
  unfold rootLn rootFn
  by_cases hi : (i : ℕ) < O.j
  · rw [if_pos hi, if_pos hi, la]
    refine tr ?_ _
    funext x
    simp only [Setup.ex, rootEx, rootSym]
    rw [if_pos (by omega), expo_single, expo_single]
  · rw [if_neg hi, if_neg hi, la]
    refine (lnN_neg hO c σ y _ (generatesAt_genAt _ _)).symm.trans (tr ?_ _)
    funext x
    have hs : O.S.Dw.p + O.S.Dw.q - 1 - (i : ℕ) = O.N - 1 - (i : ℕ) := by omega
    simp only [Setup.ex, rootEx, rootSym]
    rw [if_neg (by omega), Pi.neg_apply, expo_single, expo_single, hs]
    split_ifs <;> simp

omit hO in

private theorem detEx_eq (τ : D.what₂.Tau) : detEx O.S τ = ∑ i : Fin O.N, O.ex (τ, i) := by
  change expo O.S.Dw (detSym O.S.Dw (fun _ => false) none (DV.tauEmb D τ)) = _
  rw [detSym, GlobalTheory.OmCx.expo_finset_sum, O.S.rank_eq, Finset.sum_range]
  rfl

private theorem lnN_flatSec (B : ℝ) (τ : D.what₂.Tau) :
    Real.log ‖ratVal (flatSec O.s O.Φ c τ / detFn O c B τ (under y)) y‖ + detLn O c B τ σ y =
      lnN (O.met.h0 c σ (detEx O.S τ)) (flatSec O.s O.Φ c τ) y := by
  have hu := unitAt_flatSec_div_detFn D O c B τ (under y)
  have hg : (divOf (O.Φ.C c) (detEx O.S τ)).GeneratesAt (under y) (detFn O c B τ (under y)) :=
    generatesAt_detFn O c B τ (under y)
  have h0 : detFn O c B τ (under y) ≠ 0 := have ⟨_, _, hu⟩ := hg; left_ne_zero_of_mul hu.ne_zero
  have h1 : detLn O c B τ σ y = lnN (O.met.h0 c σ (detEx O.S τ)) (detFn O c B τ (under y)) y := by
    rw [detEx_eq, detFn, lnN_sum hO c σ y _ (fun i : Fin O.N => O.ex (τ, i)) _ fun i => generatesAt_rootFn O c B τ i (under y), detLn]
    exact Finset.sum_congr rfl fun i _ => rootLn_eq hO c σ y B τ i
  have hP := pn_pos hO c σ y _ hg
  have hn : ‖ratVal (flatSec O.s O.Φ c τ / detFn O c B τ (under y)) y‖ ≠ 0 := norm_ne_zero_iff.2 (ratVal_ne_zero hu)
  rw [h1]
  simp only [lnN]
  conv_rhs => rw [← div_mul_cancel₀ (flatSec O.s O.Φ c τ) h0]
  rw [(cxSt D.what₂.LL).pn_mul _ σ _ _ _ _ y hu.regAt hg.regularAt, Real.log_mul (pow_ne_zero 2 hn) hP.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.FlatSecConst

open GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.Toroidal in

theorem _root_.GlobalTheory.T.green_function_pullback_equality : ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (B : ℝ) (τ : D.what₂.Tau) (c : O.s.Comp)
    (g : (T.M c).Fun), (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ (gY : ∀ σ : D.what₂.LL →+* ℂ, Pts (O.var c) σ → ℝ), (∀ a z, gY ((h.man c).ε a) ((h.man c).pt a z) = g a z) →
    ∀ σ : D.what₂.LL →+* ℂ, ∃ C : ℝ, ∀ y : Pts (O.var c) σ,
      Real.log ‖ratVal (flatSec O.s O.Φ c τ / detFn O c B τ (under y)) y‖ + (detLn O c B τ σ y - gY σ y) = C := by
  intro D O hO A T H h B τ c g hg he gY hgY σ
  simp only [← add_sub_assoc, GlobalTheory.FlatSecConst.lnN_flatSec hO]
  obtain ⟨x, P, hc⟩ := hO
  let I := h.man c
  obtain ⟨a, rfl⟩ := I.ε.surjective σ
  have hφ := GlobalTheory.ShFam.Hor.isFlat_flatSec D O.A O.N O.j O.S O.κ O.s O.Φ c τ
  generalize flatSec O.s O.Φ c τ = φ at hφ
  have h0 : φ ≠ 0 := have ⟨_, _, hu⟩ := hφ (genericPoint _); left_ne_zero_of_mul hu.ne_zero
  have hu : ∀ y, (divOf (O.Φ.C c) (detEx O.S τ)).IsEqn y (Units.mk0 φ h0)⁻¹ := fun y =>
    CartierDiv.isEqn_iff_generatesAt_inv.2 (by simpa using hφ y)
  have hw : ∀ (m : Var.Met (O.var c) (I.ε a) (divOf (O.Φ.C c) (detEx O.S τ))) (p : Pts (O.var c) (I.ε a)),
      lnN (C := cxSt D.what₂.LL) m φ p = -Var.Met.wt m (Units.mk0 φ h0)⁻¹ p / 2 := fun m p => by
    have e₁ := Var.pn_frame (m := m) (y := p) (hu _)
    rw [inv_inv, Units.val_mk0] at e₁
    show Real.log ((O.Φ.C c).Y.pn _ _ m ((O.Φ.C c).Y.cx _ φ) p) / 2 = _
    rw [e₁]
    unfold Var.Met.wt
    ring
  obtain ⟨b, hb⟩ := GlobalTheory.DetHodgeExt.exists_wt_const x O.Φ c τ hu (I.ε a)
  have hs := (((GlobalTheory.metsOf_smooth D O.A O.N O.j O.S O.κ O.s x O.Φ c (I.ε a) (detEx O.S τ)).2.1.2
    (Units.mk0 φ h0)⁻¹).mono (T := Set.univ) fun p _ => ⟨trivial, hu _⟩).continuousOn isOpen_univ
  rw [continuousOn_univ] at hs
  have key : (fun z => -Var.Met.wt (refMet x O.Φ c (I.ε a) (detEx O.S τ)) (Units.mk0 φ h0)⁻¹ (I.pt a z) / 2 - g a z) =
      fun _ => -b / 2 := by
    refine Continuous.ext_on (GlobalTheory.HomChgConj.dense_compl_bd ((T.M c).bd a))
      (((hs.comp (I.pt a).continuous).neg.div_const 2).sub (GlobalTheory.HomChgConj.continuous_of_smooth (hg a)))
      continuous_const fun z hz => ?_
    have hz' := ((h.an c).Z a z).not.1 hz
    have e : g a z = -lnRatio (metsOf x O.Φ c none (I.ε a) (detEx O.S τ)) (refMet x O.Φ c (I.ε a) (detEx O.S τ))
        (I.pt a z) := by
      refine ((he a z hz).trans ((h.an c).ph _ a z hz)).trans ?_
      unfold Setup.chg
      rw [hc.hm_eq, hc.h0_eq, Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp),
        GlobalTheory.FlatSecConst.detEx_eq]
      simp only [if_true, neg_one_mul, Finset.sum_neg_distrib]
      exact congrArg Neg.neg (GlobalTheory.DetHodgeExt.lnRatio_sum (O.Φ.C c) (x.hodge _) (x.eigMet _) Finset.univ
        (fun i => O.ex (τ, i)) _)
    have e' := e.trans (congrArg Neg.neg ((lnRatio_eq (f := φ) (hφ _)
      (posAt_of_posSet (posSet_metsOf x O.Φ c none _ _) _) (posAt_of_posSet (posSet_refMet x O.Φ c _ _) _)).trans
      (congrArg₂ (· - ·) (hw (metsOf x O.Φ c none (I.ε a) (detEx O.S τ)) (I.pt a z))
        (hw (refMet x O.Φ c (I.ε a) (detEx O.S τ)) (I.pt a z)))))
    have hb' := hb _ hz'
    show -Var.Met.wt (refMet x O.Φ c (I.ε a) (detEx O.S τ)) (Units.mk0 φ h0)⁻¹ (I.pt a z) / 2 - g a z = -b / 2
    rw [e', ← hb']
    show -Var.Met.wt (refMet x O.Φ c (I.ε a) (detEx O.S τ)) (Units.mk0 φ h0)⁻¹ (I.pt a z) / 2 -
      -(-Var.Met.wt (metsOf x O.Φ c none (I.ε a) (detEx O.S τ)) (Units.mk0 φ h0)⁻¹ (I.pt a z) / 2 -
        -Var.Met.wt (refMet x O.Φ c (I.ε a) (detEx O.S τ)) (Units.mk0 φ h0)⁻¹ (I.pt a z) / 2) =
      -Var.Met.wt (metsOf x O.Φ c none (I.ε a) (detEx O.S τ)) (Units.mk0 φ h0)⁻¹ (I.pt a z) / 2
    ring
  refine ⟨-b / 2, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := (I.pt a).surjective y
  rw [hgY a z, hc.h0_eq]
  exact (congrArg (· - g a z) (hw (refMet x O.Φ c (I.ε a) (detEx O.S τ)) (I.pt a z))).trans (congrFun key z)

end

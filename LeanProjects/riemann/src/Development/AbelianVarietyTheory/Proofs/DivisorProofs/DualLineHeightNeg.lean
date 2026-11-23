import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HtTrivAndNefIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvGradedReferenceLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAdditiveInSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaRationalFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightSupportFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.DualLineHt

theorem log_norm_inverse {P1 P2 : ℝ} {V : ℂ} (k : P1 * P2 = 1) (hV : V ≠ 0) :
    Real.log (‖V⁻¹‖ ^ 2 * P2) / 2 = -(Real.log P1 / 2) - Real.log ‖V‖ := by
  have hP1 : P1 ≠ 0 := left_ne_zero_of_mul_eq_one k
  have hP2 : P2 = P1⁻¹ := eq_inv_of_mul_eq_one_right k
  have hn : ‖V‖ ≠ 0 := norm_ne_zero_iff.2 hV
  rw [hP2, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (inv_ne_zero hV))) (inv_ne_zero hP1), norm_inv, inv_pow, Real.log_inv, Real.log_inv, Real.log_pow]
  push_cast
  ring

section

variable {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp)

theorem log_pn_neg (w : Sym D.host.E →₀ ℤ) {σ : D.what₂.LL →+* ℂ} (p : Pts (O.var c) σ) :
    Real.log ((cxSt D.what₂.LL).pn _ σ _ (refMet x O.Φ c σ (expo O.S.Dw (-w)))
        ((cxSt D.what₂.LL).cx _ σ ((eqn (divOf (O.Φ.C c) (expo O.S.Dw (-w))) (under p))⁻¹ : (O.var c).Fnˣ)) p) / 2 =
      -(Real.log ((cxSt D.what₂.LL).pn _ σ _ (refMet x O.Φ c σ (expo O.S.Dw w))
        ((cxSt D.what₂.LL).cx _ σ ((eqn (divOf (O.Φ.C c) (expo O.S.Dw w)) (under p))⁻¹ : (O.var c).Fnˣ)) p) / 2) -
      Real.log ‖valAt p.1 ((eqn (divOf (O.Φ.C c) (expo O.S.Dw w)) (under p) *
        eqn (divOf (O.Φ.C c) (expo O.S.Dw (-w))) (under p) : (O.var c).Fnˣ) : (O.var c).Fn)‖ := by
  have hu := GlobalTheory.CombInd.DualComb.unitAt_eqn_mul (O.Φ.C c) w (under p)
  have hn := GlobalTheory.CombInd.DualComb.expo_neg O.S.Dw w
  unfold refMet
  generalize expo O.S.Dw (-w) = n' at hn hu ⊢
  generalize expo O.S.Dw w = n at hn hu ⊢
  subst hn
  set G := x.eigMet (embOf O.κ.e σ)
  set g := eqn (divOf (O.Φ.C c) n) (under p) with hgdef
  set g' := eqn (divOf (O.Φ.C c) (-n)) (under p) with hg'def
  have hg : (divOf (O.Φ.C c) n).IsEqn (under p) g := Base.isEqn_eqn _ _
  have hf : (divOf (O.Φ.C c) n).GeneratesAt (under p) (((g⁻¹ : (O.var c).Fnˣ) : (O.var c).Fn)) := by
    rw [Units.val_inv_eq_inv_val]; exact CartierDiv.isEqn_iff_generatesAt_inv.1 hg
  have key := pn_met_mul_neg G n hf
  have key' : (cxSt D.what₂.LL).pn _ σ _ ((O.Φ.C c).met G n) ((cxSt D.what₂.LL).cx _ σ ((g⁻¹ : (O.var c).Fnˣ) : (O.var c).Fn)) p *
      (cxSt D.what₂.LL).pn _ σ _ ((O.Φ.C c).met G (-n)) ((cxSt D.what₂.LL).cx _ σ (g : (O.var c).Fn)) p = 1 := by
    convert key using 4
    rw [Units.val_inv_eq_inv_val, inv_inv]
  have hgn : (divOf (O.Φ.C c) (-n)).IsEqn (under p) g⁻¹ := by
    rw [GlobalTheory.CombInd.DualComb.divOf_neg]; exact hg.neg
  have hreg : (divOf (O.Φ.C c) (-n)).RegularAt (under p) (g : (O.var c).Fn) := by
    have := (CartierDiv.isEqn_iff_generatesAt_inv.1 hgn).regularAt
    simpa [Units.val_inv_eq_inv_val] using this
  have hsplit : (((g')⁻¹ : (O.var c).Fnˣ) : (O.var c).Fn) =
      (((g * g')⁻¹ : (O.var c).Fnˣ) : (O.var c).Fn) * (g : (O.var c).Fn) := by
    rw [← Units.val_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hreg' : RegAt (under p) (((g * g')⁻¹ : (O.var c).Fnˣ) : (O.var c).Fn) := by
    rw [Units.val_inv_eq_inv_val]; exact hu.inv.regAt
  have hmul := (cxSt D.what₂.LL).pn_mul _ σ _ ((O.Φ.C c).met G (-n)) _ _ p hreg' hreg
  have hv0 : valAt p.1 ((g * g' : (O.var c).Fnˣ) : (O.var c).Fn) ≠ 0 := (Base.valAt_zpow p.1 hu).1
  have hinv : valAt p.1 (((g * g')⁻¹ : (O.var c).Fnˣ) : (O.var c).Fn) =
      (valAt p.1 ((g * g' : (O.var c).Fnˣ) : (O.var c).Fn))⁻¹ := by
    have := (Base.valAt_zpow p.1 hu).2 (-1)
    simpa [Units.val_inv_eq_inv_val] using this
  rw [hsplit, hmul, TrivNef.ratVal_eq_valAt, hinv]
  exact log_norm_inverse key' hv0

end

theorem valAt_inv_unit {F : Type} [Field F] {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) {u : Y.Fn}
    (hu : UnitAt (below p) u) : valAt p u⁻¹ = (valAt p u)⁻¹ := by
  have := (Base.valAt_zpow p hu).2 (-1)
  simpa using this

open Classical in

theorem ht_neg {D : D7} (O : Setup D) (hO : O.Core) (c : O.s.Comp) (z : (O.var c).X)
    (hz : IsClosed ({z} : Set (O.var c).X)) (w : Sym D.host.E →₀ ℤ)
    (hS : (Function.support fun v : HeightOneSpectrum (𝓞 D.what₂.LL) => if h : Nonempty (TrueGeo.Ext v) then
        ∑ᶠ (y : AlgPt (O.var c)) (_ : below y.1 = z), (O.adl0 c w).lg v h.some y else 0).Finite) :
    (O.adl0 c (-w)).ht z = -(O.adl0 c w).ht z := by
  obtain ⟨x, P, h⟩ := hO
  have hu := GlobalTheory.CombInd.DualComb.unitAt_eqn_mul (O.Φ.C c) w z
  obtain ⟨hGs, hPF⟩ := GlobalTheory.HtAdd.ProdFormulaPts.main D.what₂.LL (O.var c) z hz _ hu.inv
  have key := GlobalTheory.HtAdd.ht_comb ({()} : Finset Unit) (fun _ => -1) (O.adl0 c (-w)) (fun _ => O.adl0 c w) rfl
    (fun _ => rfl) hz _ (fun σ p hp => ?_) (fun v ε y hy => ?_) (fun _ _ => hS) hGs hPF
  · simpa using key
  · subst hp
    have e₁ : ∀ w, (O.adl0 c w).ci = 0 := fun _ => rfl
    have e₂ : ∀ w σ, (O.adl0 c w).m σ = refMet x O.Φ c σ (expo O.S.Dw w) := fun w σ => by
      rw [← h.h0_eq]; rfl
    have e₃ := log_pn_neg O x c w p
    have e₄ := valAt_inv_unit p.1 hu
    simp only [e₁, e₂, Pi.zero_apply, mul_zero, sub_zero, Finset.sum_singleton, Int.cast_neg, Int.cast_one,
      neg_one_mul]
    rw [TrivNef.ratVal_eq_valAt, e₄, norm_inv, Real.log_inv, ← sub_eq_add_neg]
    exact e₃
  · subst hy
    have e₃ := GlobalTheory.CombInd.DualComb.lgOf_neg (O.Φ.C c) w v ε y
    have e₄ := valAt_inv_unit y.1 hu
    simp only [Finset.sum_singleton, Int.cast_neg, Int.cast_one, neg_one_mul]
    rw [e₄, map_inv₀, Real.log_inv, ← sub_eq_add_neg]
    exact e₃

theorem main : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (z : (O.var c).X), IsClosed ({z} : Set (O.var c).X) →
    ∀ (τ : D.host.E →+* ℂ) (m : ℕ), m < O.S.Dw.mult τ →
    (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, m)) (-1))).ht z =
      -(O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, m)) 1)).ht z := by
  intro D O hO c z hz τ m hm
  obtain ⟨W⟩ := ReadsEx.nonempty_latModel hO ∅ c
  have hs : (letterOf O.S.Dw (.inl (τ, m))).isSome := by simp [letterOf, hm]
  rw [Finsupp.single_neg]
  exact ht_neg O hO c z hz _
    (CoverFinSupp.finite_support _ _ _ _ _ _ _ one_ne_zero (W.line_spec ∅ subset_rfl _ hs) z hz)

end GlobalTheory.DualLineHt

end

open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O
theorem _root_.GlobalTheory.T.dual_line_height_neg : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (z : (O.var c).X), IsClosed ({z} : Set (O.var c).X) → ∀ (τ : D.host.E →+* ℂ) (m : ℕ), m < O.S.Dw.mult τ → (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, m)) (-1))).ht z = -(O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, m)) 1)).ht z := GlobalTheory.DualLineHt.main

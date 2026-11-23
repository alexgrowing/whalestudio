import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAbsExponentLeL1Norm

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar
  GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal NNReal

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.CovHt.HTLink

theorem recVal_le : GlobalTheory.CovHt.HTDiag.DiagBound → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ)
    (pl : HeightOneSpectrum (𝓞 c.F)), p.Prime → (p : 𝓞 c.F) ∈ pl.asIdeal → ∀ w ∈ (htVals Xo c).1 pl,
    ∃ v ∈ (recVals Xo c).1 pl, ∀ (u : AllWt.Weight Dw), ∀ f ∈ secZ Xo c (exOf Dw u 0),
      v f ≤ w f + (((vLa pl (p : c.F) : ℝ) * htEx E p * l1 u : ℝ) : EReal) := by
  intro hD E _ _ _ _ H Dw l Xo c p pl hp hpl w hw
  obtain ⟨q, hq, inst, T, io, e, y₀, k, y, ho, hy, h, rfl⟩ := hw
  obtain rfl : p = q := by
    by_contra hne'
    have hne : q ≠ p := Ne.symm hne'
    obtain ⟨a, b, hab⟩ : IsCoprime (q : 𝓞 c.F) (p : 𝓞 c.F) :=
      Nat.Coprime.cast ((Nat.coprime_primes hq.out hp).2 hne)
    exact pl.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ (h.mem ho)) (Ideal.mul_mem_left _ _ hpl)))
  refine ⟨vAtV (PtV.mk (cls := algCls Xo c) (PY := Unit) (lies := fun _ _ _ _ => True) pl ho y₀ hy () trivial),
    ⟨_, rfl⟩, fun u f hf => ?_⟩
  letI := io.toAlgebra
  letI := H.starRing
  have h' : IsHTFrame p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] y₀ k y := h
  obtain ⟨-, -, -, -, z, -, hz, -⟩ := id h'
  obtain ⟨t, ht, -, hs⟩ := hD E H Dw l Xo c p T io y₀ hy k y z h hz
  have he : (0 : ℝ) ≤ vLa pl (p : c.F) := by
    have := vAdd_int_nonneg pl (a := (p : 𝓞 c.F)) (by simpa using hp.ne_zero)
    exact_mod_cast (show (0 : ℤ) ≤ vLa pl (p : c.F) by simpa [vLa, Formalism.BasicNotions.vAdd] using this)
  have hx : 0 ≤ htEx E p := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact add_nonneg (div_nonneg zero_le_one (by linarith)) (by positivity)
  have key := HTDiag.val_vw_prod_le pl p t (fun i => -exOf Dw u 0 i) (htEx E p)
    (by show -exOf Dw u 0 none = 0; rw [neg_eq_zero]; rfl) hs he hx
  have hl1 := GlobalTheory.L1WeightExponents.main E H Dw u
  change nval T.V e (evR Xo c f y₀.1) ≤ val_vw pl p (Valued.v : Valuation ℂ_[p] ℝ≥0) (evR Xo c f y) + _
  rw [FlagTan.evR_frBor hf ht, FlagTan.evR_frMap hf.1 hz, val_vw_mul, h'.val_vw_map ho]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, val_vw pl p (Valued.v : Valuation ℂ_[p] ℝ≥0)
      ((∏ i, t i ^ exOf Dw u 0 i : ℂ_[p]ˣ) : ℂ_[p]) = r := ⟨_, val_vw_of_ne pl p _ (Units.ne_zero _)⟩
  obtain ⟨r', hr'⟩ : ∃ r' : ℝ, val_vw pl p (Valued.v : Valuation ℂ_[p] ℝ≥0)
      ((∏ i, t i ^ (-exOf Dw u 0 i) : ℂ_[p]ˣ) : ℂ_[p]) = r' := ⟨_, val_vw_of_ne pl p _ (Units.ne_zero _)⟩
  have hsum : r' + r = 0 := by
    have h1 := val_vw_mul pl p (Valued.v : Valuation ℂ_[p] ℝ≥0)
      ((∏ i, t i ^ (-exOf Dw u 0 i) : ℂ_[p]ˣ) : ℂ_[p]) ((∏ i, t i ^ exOf Dw u 0 i : ℂ_[p]ˣ) : ℂ_[p])
    rw [← Units.val_mul, ← Finset.prod_mul_distrib] at h1
    simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, Units.val_one] at h1
    rw [val_vw_of_eq_one pl p _ (map_one _), hr, hr', ← EReal.coe_add] at h1
    exact_mod_cast h1.symm
  rw [hr', EReal.coe_le_coe_iff] at key
  simp only [Int.cast_neg, abs_neg] at key
  have hb : r' ≤ (vLa pl (p : c.F) : ℝ) * htEx E p * l1 u :=
    key.trans (mul_le_mul_of_nonneg_left hl1 (mul_nonneg he hx))
  rw [hr]
  generalize nval T.V e (evR Xo c f y₀.1) = N
  induction N using EReal.rec with
  | bot => exact bot_le
  | top => rw [EReal.coe_add_top, EReal.top_add_coe]
  | coe x =>
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

end GlobalTheory.CovHt.HTLink

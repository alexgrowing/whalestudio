import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLUBRangeOfMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValVwProdLe

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier
open scoped ENNReal

namespace GlobalTheory.CovHt.Link

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

abbrev unf (s : FinalTheorems S κ) : ∀ σ : κ.c.F →+* ℂ, Formalism.L2.Pj.Unf s.Xo κ.c σ N := fun σ => GlobalTheory.ThetaDictCompare.toU (s.U σ)

def wtR (L : CmList A) (u : AllWt.Weight S.Dw) : D.what₂.Tau → Fin N → ℝ :=
  fun t i => u (L.ψ t) (Fin.cast S.rank_eq.symm i)

def drSym (la : AllWt.Weight S.Dw) : Sym D.host.E →₀ ℤ :=
  ∑ z : Letter S.Dw, Finsupp.single (fun _ => false, none, .inl (z.1, z.2)) (-exOf S.Dw la 0 (some z))

theorem expo_drSym (la : AllWt.Weight S.Dw) : expo S.Dw (drSym la) = fun z => -exOf S.Dw la 0 (some z) := by
  classical
  funext x
  have e : ∀ w w' : Sym D.host.E →₀ ℤ, expo S.Dw (w + w') x = expo S.Dw w x + expo S.Dw w' x := fun w w' =>
    Finsupp.sum_add_index' (fun _ => by simp) fun _ _ _ => by split_ifs <;> simp
  let φ : (Sym D.host.E →₀ ℤ) →+ ℤ := AddMonoidHom.mk' (fun w => expo S.Dw w x) e
  change φ _ = _
  rw [drSym, map_sum, Finset.sum_eq_single x (fun z _ hz => ?_) (by simp)]
  · change expo S.Dw _ x = _
    rw [GlobalTheory.Mean4O.expo_single, if_pos (by simp [letterOf])]
  · change expo S.Dw _ x = _
    rw [GlobalTheory.Mean4O.expo_single, if_neg (by simpa [letterOf] using hz)]

variable {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

theorem divOf_drSym (la : AllWt.Weight S.Dw) : divOf (Φ.C k) (expo S.Dw (drSym la)) = (Φ.C k).Lw la := by
  rw [expo_drSym, GlobalTheory.ShFam.DeKeyTrue.divOf_neg_exOf]

def Over (Z : Comp s.Xo κ.c) : Prop := letI := (constF κ.e (Φ.C k).Y).toAlgebra; LiesOn Z (Φ.C k).y0

def IsCuspSec (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn) : Prop :=
  f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) ∧ (Φ.C k).Y.vanishOn ((Φ.C k).Lw la) f (Φ.C k).Ybd

def infSq (x : ToroidalCompactificationData s) (la : AllWt.Weight S.Dw) (σ : D.what₂.LL →+* ℂ) (f : (Φ.C k).Y.Fn) (y : Pts (Φ.C k).Y σ) : ℝ :=
  (cxSt D.what₂.LL).pn (Φ.C k).Y σ ((Φ.C k).Lw la) (GlobalTheory.ShFam.DeKeyTrue.hodgeLw x Φ k σ la)
    ((cxSt D.what₂.LL).cx (Φ.C k).Y σ f) y

def finN (la : AllWt.Weight S.Dw) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (Φ.C k).Y)
    (f : (Φ.C k).Y.Fn) : ℝ :=
  e.w (valAt y.1 (f * (eqn (divOf (Φ.C k) (expo S.Dw (drSym la))) (below y.1) : (Φ.C k).Y.Fn))) *
    Real.exp (lgOf (Φ.C k) (drSym la) v e y)

theorem finN_eq (hm : Mets (Φ.C k) (cxSt D.what₂.LL)) (la : AllWt.Weight S.Dw) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (e : Ext v) (y : AlgPt (Φ.C k).Y) (f : (Φ.C k).Y.Fn) :
    finN Φ k la v e y f = (adlOf (Φ.C k) hm (drSym la)).nrmFin v 1 f e y := by
  simp [finN, Adl.nrmFin, adlOf]

variable (κ) in

def htLog (B : ℝ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ℝ :=
  ∑ p ∈ Pad.setB κ B, -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p

theorem countVol_mono_pos (Dm d : ℕ) {a : ℕ} (ha : 0 < a) {m m' : ℕ → ℕ∞} (h : ∀ τ, 1 ≤ τ → m τ ≤ m' τ) :
    countVol Dm d a m ≤ countVol Dm d a m' :=
  limsup_le_limsup ((eventually_gt_atTop 0).mono fun k hk => ENNReal.div_le_div_right (mul_le_mul_right
    (EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (h _ (Nat.mul_pos ha hk))))) _) _)

theorem le_volSlope_of_le {δ W a : ℝ} (hδ : δ ≤ W) (hW : 0 < W) {vol : ℝ → ℝ≥0∞}
    (h : ∀ t, ENNReal.ofReal (W * (a + t)) ≤ vol t) : (a : EReal) ≤ volSlope δ vol := by
  refine ((le_volSlope_iff hW vol a).2 h).trans (iInf_mono fun t => EReal.sub_le_sub ?_ le_rfl)
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal hδ) _)

theorem le_volSlope_of_tendsto {δ W sl c C : ℝ} {Dm : ℕ} {ar dg : ℚ → ℝ} {vol : ℝ → ℝ≥0∞} (hδ : δ ≤ W) (hW : 0 < W)
    (hd : Tendsto dg (𝓝[>] 0) (𝓝 W)) (ha : Tendsto (fun r => ar r / (((Dm : ℝ) + 1) * dg r)) (𝓝[>] 0) (𝓝 sl))
    (h : ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ t, ENNReal.ofReal (ar r / ((Dm : ℝ) + 1) + dg r * (t - c - C * r)) ≤ vol t) :
    ((sl - c : ℝ) : EReal) ≤ volSlope δ vol := by
  refine le_volSlope_of_le hδ hW fun t => ?_
  have hr : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Rat.continuous_coe_real.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun r : ℚ => dg r * (ar r / (((Dm : ℝ) + 1) * dg r)) + dg r * (t - c - C * r)) (𝓝[>] 0)
      (𝓝 (W * sl + W * (t - c - C * 0))) :=
    (hd.mul ha).add (hd.mul (tendsto_const_nhds.sub (hr.const_mul C)))
  have e : W * sl + W * (t - c - C * 0) = W * (sl - c + t) := by ring
  rw [e] at h1
  refine le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp h1) ?_
  filter_upwards [h, hd.eventually (lt_mem_nhds hW)] with r h2 h3
  refine le_of_eq_of_le (congrArg ENNReal.ofReal ?_) (h2 t)
  have := h3.ne'
  field_simp

end GlobalTheory.CovHt.Link

end

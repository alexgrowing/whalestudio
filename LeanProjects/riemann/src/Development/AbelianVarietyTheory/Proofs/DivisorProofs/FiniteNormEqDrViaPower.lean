import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrViaNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LgOfSingleNegOneEqNeg
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CovHt.Link

section Free
open Formalism.L2.Geo GlobalTheory.Toroidal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

noncomputable def stepSumVia (w : Sym E →₀ ℤ) (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (y : Sp K ⟶ Y.Y.X)
    (φ : K →+* ℂ_[p]) : ℝ :=
  w.sum fun a n => (n : ℝ) * lnStep Z.t
      (spMap (φ.comp (Scheme.stalkClosedPointTo y).hom) ≫ stalkPt Y.Y (below y) ≫ Y.π ≫ genι Z)
      (fun τ i => spMap (dualMap (φ.comp (Scheme.stalkClosedPointTo y).hom)) ≫
        (Y.gr_spec (below y)).choose_spec.choose.v τ i) p (a.1 p) a.2.2

theorem lgOf_eq_stepSumVia (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) [hp : Fact (resP v).Prime] (ε : Ext v)
    (y : AlgPt Y.Y) :
    lgOf Y w v ε y = Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) * stepSumVia Y w (resP v) y.1 (ioOf (resP v) ε) := by
  obtain ⟨hp⟩ := hp
  unfold lgOf stepSumVia
  exact dif_pos hp

end Free

theorem drVia_eq_stepSumVia {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)
    (la : AllWt.Weight S.Dw) (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (y : Sp K ⟶ (Φ.C k).Y.X)
    (φ : K →+* ℂ_[p]) (f : (Φ.C k).Y.Fn) :
    drVia Φ k la p y φ f = ‖φ (GlobalTheory.TrueGeo.valAt y (f * ((∏ z : Letter S.Dw,
      (((Φ.C k).gr_spec (below y)).choose_spec.choose_spec.choose z.1 z.2) ^
      expo S.Dw (drSym la) z : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn)))‖ * Real.exp (stepSumVia (Φ.C k) (drSym la) p y φ) := by
  unfold drVia stepSumVia
  rfl

theorem mul_exp_log_add {A B X S c : ℝ} (hB : 0 < B) (hX : 0 ≤ X) (h : A * B = X ^ c) :
    A * Real.exp (Real.log B + c * S) = (X * Real.exp S) ^ c := by
  rw [Real.exp_add, Real.exp_log hB, Real.mul_rpow hX (Real.exp_pos _).le, ← Real.exp_mul, ← mul_assoc, h, mul_comm c]

theorem residueCharacteristic_eq_of_mem {F : Type} [Field F] [NumberField F] (p : ℕ) [hp : Fact p.Prime] (v : HeightOneSpectrum (𝓞 F))
    (hv : (p : 𝓞 F) ∈ v.asIdeal) : resP v = p := by
  by_contra hne
  have hcop : Nat.gcd (resP v) p = 1 := ((Nat.coprime_primes (residueCharacteristic_prime v) hp.out).2 hne)
  have h1 := congrArg (Int.cast : ℤ → 𝓞 F) (Nat.gcd_eq_gcd_ab (resP v) p)
  rw [hcop] at h1
  push_cast at h1
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (residueCharacteristic_mem v)) (Ideal.mul_mem_right _ _ hv)

theorem w_eq_norm_ioOf_rpow {F : Type} [Field F] [NumberField F] (p : ℕ) [hp : Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) (e : Ext v) (z : AlgebraicClosure F) :
    e.w z = ‖ioOf p e z‖ ^ (-Real.log (e.w (p : AlgebraicClosure F)) / Real.log p) := by
  have hq := hp.out
  have hw1 : e.w (p : AlgebraicClosure F) < 1 := by
    have h : (p : AlgebraicClosure F) = algebraMap F _ (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
    rw [h, e.w_alg]
    exact (v.adicAbv_coe_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hv
  have hw0 : 0 < e.w (p : AlgebraicClosure F) := e.w.pos (Nat.cast_ne_zero.2 hq.ne_zero)
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hc : 0 < -Real.log (e.w (p : AlgebraicClosure F)) / Real.log p := div_pos (neg_pos.2 (Real.log_neg hw0 hw1)) hlp
  have hio := ioOf_le_one_iff p hv e
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow hc.ne']
  · have h := log_w_eq p e (ioOf p e) hio z
    have hn : 0 < ‖ioOf p e z‖ := norm_pos_iff.2 ((map_ne_zero _).2 hz)
    rw [Real.rpow_def_of_pos hn, mul_comm, ← h, Real.exp_log (e.w.pos hz)]

theorem w_valAt_mul_change {F : Type} [Field F] [NumberField F] {Y : Var F} {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    (y : AlgPt Y) {Δ : Y.Dv} {t u : Y.Fnˣ} (ht : Δ.IsEqn (below y.1) t) (hu : Δ.IsEqn (below y.1) u) {f : Y.Fn}
    (hf : f ∈ Y.H0 Δ) :
    0 < e.w (valAt y.1 ((t * u⁻¹ : Y.Fnˣ) : Y.Fn)) ∧
      e.w (valAt y.1 (f * (u : Y.Fn))) * e.w (valAt y.1 ((t * u⁻¹ : Y.Fnˣ) : Y.Fn)) = e.w (valAt y.1 (f * (t : Y.Fn))) := by
  have hU : UnitAt (below y.1) ((t * u⁻¹ : Y.Fnˣ) : Y.Fn) := by
    simpa [div_eq_mul_inv] using hu.iff_unitAt.1 ht
  have hR : RegAt (below y.1) (f * (u : Y.Fn)) := hu.regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hf (below y.1))
  refine ⟨e.w.pos (SmallSec.valAt_ne_zero hU), ?_⟩
  rw [← map_mul, ← SmallSec.valAt_mul hR hU.regAt, mul_assoc, ← Units.val_mul, mul_comm t, ← mul_assoc, mul_inv_cancel,
    one_mul]

section Free
open Formalism.L2.Geo GlobalTheory.Toroidal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem w_mul_exp_lgOf (w : Sym E →₀ ℤ) (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 F))
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (ε : Ext v) (y : AlgPt Y.Y) {f : Y.Y.Fn} (hf : f ∈ Y.Y.H0 (divOf Y (expo Dw w))) :
    ε.w (valAt y.1 (f * (eqn (divOf Y (expo Dw w)) (below y.1) : Y.Y.Fn))) * Real.exp (lgOf Y w v ε y) =
      (‖ioOf p ε (valAt y.1 (f * ((∏ z : Letter Dw,
        ((Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2) ^ expo Dw w z : Y.Y.Fnˣ) : Y.Y.Fn)))‖ *
        Real.exp (stepSumVia Y w p y.1 (ioOf p ε))) ^ (-Real.log (ε.w (p : AlgebraicClosure F)) / Real.log p) := by
  have hw := w_eq_norm_ioOf_rpow p v hv ε
  obtain rfl : resP v = p := residueCharacteristic_eq_of_mem p v hv
  obtain ⟨hb, hm⟩ := w_valAt_mul_change ε y
    (GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.isEqn_prod Y (below y.1) (expo Dw w))
    (Base.isEqn_eqn (divOf Y (expo Dw w)) (below y.1)) hf
  rewrite [lgOf_eq_stepSumVia]
  exact mul_exp_log_add hb (norm_nonneg _) (hm.trans (hw _))

end Free

theorem finN_eq_drVia_rpow : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn), f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 D.what₂.LL)), (p : 𝓞 D.what₂.LL) ∈ v.asIdeal → ∀ (e : Ext v) (y : AlgPt (Φ.C k).Y), finN Φ k la v e y f = drVia Φ k la p y.1 (ioOf p e) f ^ (-Real.log (e.w p) / Real.log p) := by
  intro D A N j S κ s Φ k la f hf p _ v hv e y
  have hf' : f ∈ (Φ.C k).Y.H0 (divOf (Φ.C k) (expo S.Dw (drSym la))) := by
    rewrite [divOf_drSym Φ k la]
    exact hf
  have h := w_mul_exp_lgOf (Φ.C k) (drSym la) p v hv e y hf'
  rewrite [drVia_eq_stepSumVia]
  unfold finN
  exact h

end GlobalTheory.CovHt.Link

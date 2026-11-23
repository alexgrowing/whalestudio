import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

def IntOff {K : Type} [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  ∀ w, (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n

def logSum (B : Finset ℕ) : ℝ := ∑ p ∈ B, Real.log p

theorem intOff_zero {K : Type} [Field K] [NumberField K] (B : Finset ℕ) :
    IntOff B (0 : HeightOneSpectrum (𝓞 K) → ℝ) := fun _ _ => ⟨0, by simp⟩

theorem IntOff.add {K : Type} [Field K] [NumberField K] {B : Finset ℕ} {ρ ρ' : HeightOneSpectrum (𝓞 K) → ℝ}
    (h : IntOff B ρ) (h' : IntOff B ρ') : IntOff B (ρ + ρ') := fun w hw => by
  obtain ⟨n, hn⟩ := h w hw
  obtain ⟨m, hm⟩ := h' w hw
  exact ⟨n + m, by simp [hn, hm]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

structure TwSec (Z : Comp Xo c) (G₀ : WTZ E) : Type where
  even : Even G₀.2

  sig : Rul Xo c

  inv : Rul Xo c
  sig_mem : sig ∈ secZ Xo c (exZ Dw G₀)
  inv_mem : inv ∈ secZ Xo c (-exZ Dw G₀)
  idem_sig : idem Z * sig = sig
  idem_inv : idem Z * inv = inv
  mul_inv : sig * inv = idem Z

  cInf : (c.F →+* ℂ) → ℝ
  cInf_pos : ∀ σ, 0 < cInf σ
  norm_inf : ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) x G₀ sig z = cInf σ
  cusp_sig : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * sig ∈ cuspOn U Z (G + G₀)
  cusp_inv : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z (G + G₀), f * inv ∈ cuspOn U Z G

  lo : HeightOneSpectrum (𝓞 c.F) → ℝ

  hi : HeightOneSpectrum (𝓞 c.F) → ℝ
  lo_le : ∀ w, ∀ v ∈ valOn Z w, ((lo w : ℝ) : EReal) ≤ v sig
  le_hi : ∀ w, ∀ v ∈ valOn Z w, v sig ≤ ((hi w : ℝ) : EReal)
  finite_lo : (Function.support lo).Finite
  finite_hi : (Function.support hi).Finite

  pts : HasPts U Z := by assumption

variable {U x}

def TwSec.degLo {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) : ℝ := lineDeg s.cInf s.lo

theorem mul_smul_idem_mem {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (a : c.F) :
    f * (a • idem Z) ∈ cuspOn U Z G := by
  have h : idem Z * f = f := idem_mul_eq (e := exZ Dw G) ⟨cuspW_le_secZ G hf.1, hf.2⟩
  rw [mul_smul_comm, mul_comm f, h]
  exact Submodule.smul_mem _ _ hf

theorem exZ_add_eq (G G' : WTZ E) : exZ Dw (G + G') = exZ Dw G + exZ Dw G' := funext fun i => exZ_add _ _ i

theorem exZ_neg_eq (G : WTZ E) : exZ Dw (-G) = -exZ Dw G := by
  funext i; cases i <;> rfl

namespace TwSec

variable {Z : Comp Xo c} {G₀ G₁ : WTZ E}

theorem sig_mem_suppOn (s : TwSec U x Z G₀) : s.sig ∈ suppOn Z := by
  rw [← s.idem_sig, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem inv_mem_suppOn (s : TwSec U x Z G₀) : s.inv ∈ suppOn Z := by
  rw [← s.idem_inv, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem sig_ne_zero (s : TwSec U x Z G₀) : s.sig ≠ 0 := fun h0 => by
  obtain ⟨z, hz⟩ := (s.pts.1 c.F.val.toRingHom).1
  have h1 := s.norm_inf _ z hz
  rw [h0, ← zero_smul c.F (0 : Rul Xo c), homN_smul, map_zero, norm_zero, zero_mul] at h1
  exact (s.cInf_pos _).ne h1

theorem lo_le_hi (s : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)) : s.lo w ≤ s.hi w := by
  obtain ⟨v, hv⟩ := s.pts.2 w
  exact EReal.coe_le_coe_iff.1 ((s.lo_le w v hv).trans (s.le_hi w v hv))

theorem cInf_eq (s t : TwSec U x Z G₀) (e : s.sig = t.sig) : s.cInf = t.cInf := funext fun σ => by
  obtain ⟨z, hz⟩ := (s.pts.1 σ).1
  rw [← s.norm_inf σ z hz, ← t.norm_inf σ z hz, e]

theorem cInf_congr (s : TwSec U x Z G₀) {σ σ' : c.F →+* ℂ} (h : goodOf c σ = goodOf c σ') : s.cInf σ = s.cInf σ' := by
  obtain ⟨z, hz⟩ := (s.pts.1 σ).1
  have h2 := s.norm_inf σ'
  rw [← h] at h2
  rw [← s.norm_inf σ z hz, h2 z hz]

theorem homN_mul_sig (s : TwSec U x Z G₀) {G : WTZ E} (hG : Even G.2) (f : Rul Xo c) {σ : c.F →+* ℂ} {z}
    (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) z = homN (U (goodOf c σ)) x G f z * s.cInf σ := by
  rw [homN_mul _ x hG s.even _ _ _ hz.1, s.norm_inf σ z hz]

theorem exists_val (s : TwSec U x Z G₀) {w} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z w) :
    ∃ b : ℝ, v s.sig = b ∧ v s.inv = ((-b : ℝ) : EReal) ∧ s.lo w ≤ b ∧ b ≤ s.hi w := by
  have h1 := s.lo_le w v hv
  have h2 := s.le_hi w v hv
  have h := (isVal_valOn hv).mul s.sig s.inv
  rw [s.mul_inv, val_idem hv] at h
  lift v s.sig to ℝ using ⟨(h2.trans_lt (EReal.coe_lt_top _)).ne, ((EReal.bot_lt_coe _).trans_le h1).ne'⟩ with a
  have ht : v s.inv ≠ ⊤ := fun h' => by rw [h', EReal.coe_add_top] at h; exact EReal.zero_ne_top h
  lift v s.inv to ℝ using ⟨ht, (isVal_valOn hv).ne_bot s.inv⟩ with b
  rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at h
  exact ⟨a, rfl, EReal.coe_eq_coe_iff.2 (by linarith), EReal.coe_le_coe_iff.1 h1, EReal.coe_le_coe_iff.1 h2⟩

def copy (s : TwSec U x Z G₀) (h : G₀ = G₁) : TwSec U x Z G₁ :=
  { s with
    even := h ▸ s.even, sig_mem := h ▸ s.sig_mem, inv_mem := h ▸ s.inv_mem, norm_inf := h ▸ s.norm_inf,
    cusp_sig := h ▸ s.cusp_sig, cusp_inv := h ▸ s.cusp_inv }

def mul (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) : TwSec U x Z (G₀ + G₁) where
  even := s.even.add t.even
  sig := s.sig * t.sig
  inv := s.inv * t.inv
  sig_mem := exZ_add_eq (Dw := Dw) G₀ G₁ ▸ mul_mem_secZ s.sig_mem t.sig_mem
  inv_mem := by rw [exZ_add_eq, neg_add]; exact mul_mem_secZ s.inv_mem t.inv_mem
  idem_sig := by rw [← mul_assoc, s.idem_sig]
  idem_inv := by rw [← mul_assoc, s.idem_inv]
  mul_inv := by rw [mul_mul_mul_comm, s.mul_inv, t.mul_inv, idem_mul_idem]
  cInf := s.cInf * t.cInf
  cInf_pos σ := mul_pos (s.cInf_pos σ) (t.cInf_pos σ)
  norm_inf σ z hz := by rw [t.homN_mul_sig s.even _ hz, s.norm_inf σ z hz]; rfl
  cusp_sig G hG f hf := by
    rw [← mul_assoc, ← add_assoc]
    exact t.cusp_sig _ (hG.add s.even) _ (s.cusp_sig G hG f hf)
  cusp_inv G hG f hf := by
    rw [← add_assoc] at hf
    rw [mul_comm s.inv, ← mul_assoc]
    exact s.cusp_inv G hG _ (t.cusp_inv _ (hG.add s.even) f hf)
  lo := s.lo + t.lo
  hi := s.hi + t.hi
  lo_le w v hv := by
    rw [(isVal_valOn hv).mul, Pi.add_apply, EReal.coe_add]; exact add_le_add (s.lo_le w v hv) (t.lo_le w v hv)
  le_hi w v hv := by
    rw [(isVal_valOn hv).mul, Pi.add_apply, EReal.coe_add]; exact add_le_add (s.le_hi w v hv) (t.le_hi w v hv)
  finite_lo := (s.finite_lo.union t.finite_lo).subset (Function.support_add _ _)
  finite_hi := (s.finite_hi.union t.finite_hi).subset (Function.support_add _ _)
  pts := s.pts

theorem degLo_mul (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) : (s.mul t).degLo = s.degLo + t.degLo :=
  lineDeg_mul s.cInf_pos t.cInf_pos s.finite_lo t.finite_lo

def symm (s : TwSec U x Z G₀) : TwSec U x Z (-G₀) where
  even := s.even.neg
  sig := s.inv
  inv := s.sig
  sig_mem := exZ_neg_eq (Dw := Dw) G₀ ▸ s.inv_mem
  inv_mem := by rw [exZ_neg_eq, neg_neg]; exact s.sig_mem
  idem_sig := s.idem_inv
  idem_inv := s.idem_sig
  mul_inv := by rw [mul_comm, s.mul_inv]
  cInf := s.cInf⁻¹
  cInf_pos σ := inv_pos.2 (s.cInf_pos σ)
  norm_inf σ z hz := by
    have h := s.homN_mul_sig (G := -G₀) s.even.neg s.inv hz
    rw [neg_add_cancel, mul_comm s.inv, s.mul_inv, homN_idem _ x hz.1 hz.2 ((s.pts.1 σ).2 z hz _)] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  cusp_sig G hG f hf := s.cusp_inv _ (hG.add s.even.neg) f (by rwa [neg_add_cancel_right])
  cusp_inv G hG f hf := by
    have h := s.cusp_sig _ (show Even (G + -G₀).2 from hG.add s.even.neg) f hf
    rwa [neg_add_cancel_right] at h
  lo := -s.hi
  hi := -s.lo
  lo_le w v hv := by
    obtain ⟨b, -, h, -, h'⟩ := s.exists_val hv
    rw [h]; exact EReal.coe_le_coe_iff.2 (neg_le_neg h')
  le_hi w v hv := by
    obtain ⟨b, -, h, h', -⟩ := s.exists_val hv
    rw [h]; exact EReal.coe_le_coe_iff.2 (neg_le_neg h')
  finite_lo := by simpa using s.finite_hi
  finite_hi := by simpa using s.finite_lo
  pts := s.pts

def ofConst {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ)
    (hδ : (Function.support δ).Finite)
    (h₁ : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s.sig ∈ cuspOn U Z (G + wtOf Dw la 0))
    (h₂ : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z (G + wtOf Dw la 0), f * s.inv ∈ cuspOn U Z G) :
    TwSec U x Z (wtOf Dw la 0) where
  even := even_wtOf _ _
  sig := s.sig
  inv := s.inv
  sig_mem := s.sig_mem
  inv_mem := s.inv_mem
  idem_sig := s.idem_sig
  idem_inv := s.idem_inv
  mul_inv := s.mul_inv
  cInf := s.cInf
  cInf_pos := s.cInf_pos
  norm_inf _ _ hz := s.homN_eq hz
  cusp_sig := h₁
  cusp_inv := h₂
  lo := δ + s.rho_vw
  hi := δ + s.rho_vw
  lo_le _ _ hv := (s.val_eq hv).ge
  le_hi _ _ hv := (s.val_eq hv).le
  finite_lo := (hδ.union s.finite_rho).subset (Function.support_add _ _)
  finite_hi := (hδ.union s.finite_rho).subset (Function.support_add _ _)
  pts := s.hasPts

theorem degLo_ofConst {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ)
    (hδ : (Function.support δ).Finite) (h₁ h₂) :
    (ofConst s hδ h₁ h₂).degLo = s.deg + ∑ᶠ w, δ w * lw c.F w := by
  have := lineDeg_mul (r := 1) (fun _ => one_pos) s.cInf_pos hδ s.finite_rho
  rw [one_mul] at this
  refine this.trans ?_
  simp [lineDeg, ConstSec.deg, add_comm]

variable (x) in

def const (h : HasPts U Z) (a : c.F) (ha : a ≠ 0) : TwSec U x Z 0 :=
  (ofConst ((ConstSec.one x h).smul a ha) (by simp)
    (fun G _ f hf => by rw [wtOf_zero, add_zero]; exact mul_smul_idem_mem hf a)
    (fun G _ f hf => by rw [wtOf_zero, add_zero] at hf; exact mul_smul_idem_mem hf a⁻¹)).copy wtOf_zero

theorem const_spec (h : HasPts U Z) (a : c.F) (ha : a ≠ 0) :
    (const x h a ha).sig = a • idem Z ∧ (∀ σ, (const x h a ha).cInf σ = ‖σ a‖) ∧
      (∀ w, (const x h a ha).lo w = vAdd w a) ∧ (∀ w, (const x h a ha).hi w = vAdd w a) ∧
      (const x h a ha).degLo = 0 := by
  have h1 : ∀ σ, (const x h a ha).cInf σ = ‖σ a‖ := fun σ => mul_one _
  have h2 : ∀ w, (const x h a ha).lo w = vAdd w a := fun w => (zero_add _).trans (add_zero _)
  refine ⟨rfl, h1, h2, h2, ?_⟩
  rw [degLo, funext h1, funext h2]
  exact lineDeg_num ha

end TwSec

theorem twSec_inhabited :
    (1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) →
      ∀ (Z : Comp Xo c) (a : c.F), a ≠ 0 → ∃ s : TwSec U x Z 0, s.sig = a • idem Z ∧ (∀ σ, s.cInf σ = ‖σ a‖) ∧
        (∀ w, s.lo w = vAdd w a) ∧ s.degLo = 0) ∧
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E)
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q)) (Z : Comp Xo c),
      1 ≤ Dw.p ∧ (∀ σ, GoodEmb c σ → IsUnf (U σ)) ∧ ∀ a : c.F, a ≠ 0 →
        ∃ s : TwSec U x Z 0, s.sig = a • idem Z ∧ (∀ σ, s.cInf σ = ‖σ a‖) ∧ (∀ w, s.lo w = vAdd w a) ∧
          s.degLo = 0 := by
  refine ⟨fun hpq hg hU Z a ha => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, -, h4⟩ := TwSec.const_spec (x := x) (hasPts U hpq hg hU Z) a ha
    exact ⟨_, h1, h2, h3, h4⟩
  · obtain ⟨E, _, _, _, H, Dw, l, Xo, c, U, Z, τ, hp, hU, ⟨s⟩⟩ := GlobalTheory.FlatLine.Definite.exists_flatSec x
    refine ⟨E, _, _, _, H, Dw, l, Xo, c, U, Z, hp, hU, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3, -, h4⟩ := TwSec.const_spec (x := x) s.hasPts a ha
    exact ⟨_, h1, h2, h3, h4⟩

variable (Xo c) in

def UnramPts (B : Finset ℕ) : Prop :=
  ∀ (Z : Comp Xo c) (w : HeightOneSpectrum (𝓞 c.F)), (∀ p ∈ B, ((p : ℕ) : 𝓞 c.F) ∉ w.asIdeal) →
    ∃ v ∈ valOn Z w, ∀ f : Rul Xo c, v f = ⊤ ∨ ∃ n : ℤ, v f = ((n : ℝ) : EReal)

def badPrimes (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) : Finset ℕ :=
  (2 * H.d * (discr E).natAbs * l.M').primeFactors

theorem badPrimes_prime (p : ℕ) (hp : p ∈ badPrimes H l) : p.Prime := Nat.prime_of_mem_primeFactors hp

theorem UnramPts.mono {B B' : Finset ℕ} (h : UnramPts Xo c B) (hB : B ⊆ B') : UnramPts Xo c B' :=
  fun Z w hw => h Z w fun p hp => hw p (hB hp)

theorem mem_badPrimes {p : ℕ} :
    p ∈ badPrimes H l ↔ p.Prime ∧ (p = 2 ∨ p = H.d ∨ p ∣ (discr E).natAbs ∨ p ∣ l.M ∨ p ∣ l.A) := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) hD) hM
  rw [badPrimes, Nat.mem_primeFactors_of_ne_zero hne]
  refine and_congr_right fun hp => ?_
  simp only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp Nat.prime_two, Nat.prime_dvd_prime_iff_eq hp H.d_prime,
    Level.M', hp.dvd_lcm, or_assoc]

theorem UnramPts.of_index_one {B : Finset ℕ}
    (h : ∀ (Z : Comp Xo c) (w : HeightOneSpectrum (𝓞 c.F)), (∀ p ∈ B, ((p : ℕ) : 𝓞 c.F) ∉ w.asIdeal) →
      ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y) :
    UnramPts Xo c B := fun Z w hw => by
  obtain ⟨T, ι, y, ho, hy⟩ := h Z w hw
  refine ⟨_, ⟨PtV.mk w ho y hy () trivial, rfl⟩, fun f => ?_⟩
  show nval T.V 1 (evI y f) = ⊤ ∨ ∃ n : ℤ, nval T.V 1 (evI y f) = _
  by_cases h0 : evI y f = 0
  · rw [h0, nval_zero]; exact Or.inl rfl
  · exact Or.inr ⟨vV T.V (evI y f), by rw [nval_of_ne h0]; simp⟩

example : 2 ∈ badPrimes H l := mem_badPrimes.2 ⟨Nat.prime_two, Or.inl rfl⟩

example : logSum {2, 3} = Real.log 2 + Real.log 3 := by simp [logSum]

example {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ¬ IntOff ∅ (fun _ : HeightOneSpectrum (𝓞 K) => (1 / 2 : ℝ)) := fun h => by
  obtain ⟨n, hn⟩ := h w (by simp)
  have h2 : (1 : ℝ) = 2 * n := by simp only at hn; linarith
  have h3 : (1 : ℤ) = 2 * n := by exact_mod_cast h2
  omega

end GlobalTheory.FlatTw

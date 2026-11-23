import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem exZ_zero_model : exZ Dw (0 : WTZ E) = 0 := by
  funext i; cases i <;> rfl

theorem mul_smul_idem_mem_cuspOn {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (a : c.F) :
    f * (a • idem Z) ∈ cuspOn U Z G := by
  have h : idem Z * f = f := idem_mul_eq (e := exZ Dw G) ⟨cuspW_le_secZ G hf.1, hf.2⟩
  rw [mul_smul_comm, mul_comm, h]
  exact Submodule.smul_mem _ _ hf

variable (x) in

def TwSec.constModel {Z : Comp Xo c} (h : HasPts U Z) (a : c.F) (ha : a ≠ 0) : TwSec U x Z 0 where
  even := ⟨0, rfl⟩
  sig := a • idem Z
  inv := a⁻¹ • idem Z
  sig_mem := by rw [exZ_zero_model]; exact Submodule.smul_mem _ _ (idem_mem_secZ Z)
  inv_mem := by rw [exZ_zero_model, neg_zero]; exact Submodule.smul_mem _ _ (idem_mem_secZ Z)
  idem_sig := by rw [mul_smul_comm, idem_mul_idem]
  idem_inv := by rw [mul_smul_comm, idem_mul_idem]
  mul_inv := (smul_mul_inv_smul ha _ _).trans (idem_mul_idem Z)
  cInf := fun σ => ‖σ a‖
  cInf_pos σ := norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  norm_inf σ z hz := by
    rw [homN_smul, homN_idem _ x hz.1 hz.2 ((h.1 σ).2 z hz _), norm_goodOf, mul_one]
  cusp_sig G _ f hf := by rw [add_zero]; exact mul_smul_idem_mem_cuspOn hf a
  cusp_inv G _ f hf := by rw [add_zero] at hf; exact mul_smul_idem_mem_cuspOn hf a⁻¹
  lo := fun w => (vAdd w a : ℝ)
  hi := fun w => (vAdd w a : ℝ)
  lo_le w v hv := by rw [(isVal_valOn hv).smul _ _ ha, val_idem hv, add_zero]
  le_hi w v hv := by rw [(isVal_valOn hv).smul _ _ ha, val_idem hv, add_zero]
  finite_lo := finite_vAdd ha
  finite_hi := finite_vAdd ha

theorem TwSec.constModel_spec {Z : Comp Xo c} (h : HasPts U Z) (a : c.F) (ha : a ≠ 0) :
    (TwSec.constModel x h a ha).degLo = 0 ∧ IntOff ∅ (TwSec.constModel x h a ha).lo :=
  ⟨lineDeg_num ha, fun w _ => ⟨vAdd w a, rfl⟩⟩

theorem exists_twSec_const (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) (a : c.F) (ha : a ≠ 0) :
    ∃ s : TwSec U x Z 0, s.sig = a • idem Z ∧ (∀ σ, s.cInf σ = ‖σ a‖) ∧ (∀ w, s.lo w = vAdd w a) ∧ s.degLo = 0 :=
  ⟨TwSec.constModel x (hasPts U hpq hg hU Z) a ha, rfl, fun _ => rfl, fun _ => rfl, lineDeg_num ha⟩

theorem TwSec.lo_le_hi_of_hasPts {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) (h : HasPts U Z)
    (w : HeightOneSpectrum (𝓞 c.F)) : s.lo w ≤ s.hi w := by
  obtain ⟨v, hv⟩ := h.2 w
  exact EReal.coe_le_coe_iff.1 ((s.lo_le w v hv).trans (s.le_hi w v hv))

theorem TwSec.cInf_eq_of_hasPts {Z : Comp Xo c} {G₀ : WTZ E} (s t : TwSec U x Z G₀) (h : HasPts U Z)
    (e : s.sig = t.sig) : s.cInf = t.cInf := funext fun σ => by
  obtain ⟨z, hz⟩ := (h.1 σ).1
  rw [← s.norm_inf σ z hz, ← t.norm_inf σ z hz, e]

theorem TwSec.sig_ne_zero_of_hasPts {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) (h : HasPts U Z) :
    s.sig ≠ 0 := fun h0 => by
  obtain ⟨z, hz⟩ := (h.1 c.F.val.toRingHom).1
  have h1 := s.norm_inf _ z hz
  rw [h0, ← zero_smul c.F (0 : Rul Xo c), homN_smul, map_zero, norm_zero, zero_mul] at h1
  exact (s.cInf_pos _).ne h1

theorem unramPts_of_index_one {B : Finset ℕ}
    (h : ∀ (Z : Comp Xo c) (w : HeightOneSpectrum (𝓞 c.F)), (∀ p ∈ B, ((p : ℕ) : 𝓞 c.F) ∉ w.asIdeal) →
      ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y) :
    UnramPts Xo c B := fun Z w hw => by
  obtain ⟨T, ι, y, ho, hy⟩ := h Z w hw
  refine ⟨_, ⟨PtV.mk w ho y hy () trivial, rfl⟩, fun f => ?_⟩
  show nval T.V 1 (evI y f) = ⊤ ∨ ∃ n : ℤ, nval T.V 1 (evI y f) = _
  by_cases h0 : evI y f = 0
  · rw [h0, nval_zero]; exact Or.inl rfl
  · exact Or.inr ⟨vV T.V (evI y f), by rw [nval_of_ne h0]; simp⟩

theorem mem_badPrimes_iff {p : ℕ} (hp : p.Prime) :
    p ∈ badPrimes H l ↔ p = 2 ∨ p = H.d ∨ p ∣ (discr E).natAbs ∨ p ∣ l.M ∨ p ∣ l.A := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) hD) hM
  rw [badPrimes, Nat.mem_primeFactors_of_ne_zero hne]
  simp only [hp, true_and, hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_two, Nat.prime_dvd_prime_iff_eq hp H.d_prime, Level.M', hp.dvd_lcm,
    or_assoc]

theorem not_intOff_half {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ¬ IntOff ∅ (fun _ : HeightOneSpectrum (𝓞 K) => (1 / 2 : ℝ)) := fun h => by
  obtain ⟨n, hn⟩ := h w (by simp)
  have h2 : (1 : ℝ) = 2 * n := by simp only at hn; linarith
  have h3 : (1 : ℤ) = 2 * n := by exact_mod_cast h2
  omega

theorem mem_holSub_model {Cp : Type} (X : Cp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) :
    P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem isSec_inv (X : Data E r) {la la' : Wt X.Ψ r} (hla : la' + la = 0) {e s t : Frame X.Ψ r → ℂ}
    (he : X.IsSec 0 e) (ht : X.IsSec la t) (hee : e * e = e) (hes : e * s = s) (het : e * t = t) (hst : s * t = e) :
    X.IsSec la' s := by
  have ee : ∀ y, e y * e y = e y := congrFun hee
  have es : ∀ y, e y * s y = s y := congrFun hes
  have et : ∀ y, e y * t y = t y := congrFun het
  have st : ∀ y, s y * t y = e y := congrFun hst
  have e01 : ∀ y, e y = 0 ∨ e y = 1 := fun y => IsIdempotentElem.iff_eq_zero_or_one.1 (ee y)
  have key : ∀ y y' (a b : ℂ), b * a = 1 → e y' = e y → t y' = a * t y → s y' = b * s y := by
    intro y y' a b hab h1 h2
    have := es y; have := es y'; have := st y; have := st y'
    rcases e01 y with h | h
    · rw [← es y', ← es y, h1, h]; simp
    · have h3 := st y
      have h4 := st y'
      rw [h1, h2, h] at h4
      rw [h] at h3
      linear_combination (-s y') * h3 + (b * s y) * h4 - (s y' * s y * t y) * hab
  have hχ0 : ∀ γ ∈ X.Γ, X.χ 0 γ = 1 := fun γ hγ => by
    obtain ⟨n, hn, h⟩ := X.χ_fin 0
    have h1 := X.χ_add 0 0 γ hγ
    rw [add_zero] at h1
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 h1.symm with h2 | h2
    · have := h γ hγ
      rw [h2, zero_pow hn.ne'] at this
      exact absurd this zero_ne_one
    · exact h2
  refine ⟨?_, fun y hy b hb => key _ _ _ _ ?_ ?_ (ht.2.1 y hy b hb), fun γ hγ y hy => key _ _ _ _ ?_ ?_ (ht.2.2 γ hγ y hy)⟩
  · have hne : ∀ y, t y + 1 - e y ≠ 0 := fun y => by
      rcases e01 y with h | h
      · rw [← et y, h]; simp
      · have h3 := st y
        rw [h] at h3 ⊢
        intro h0
        have : t y = 0 := by linear_combination h0
        rw [this, mul_zero] at h3
        exact zero_ne_one h3
    have : s = fun y => e y * (t y + 1 - e y)⁻¹ := funext fun y => by
      rw [eq_mul_inv_iff_mul_eq₀ (hne y)]
      linear_combination st y - es y
    rw [this]
    exact he.1.fun_mul (((ht.1.add_const 1).fun_sub he.1).fun_inv fun y _ => hne y)
  · have hd : ∀ τ i, b τ i i ≠ 0 := fun τ i h0 => (hb τ).1 (by
      rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0)
    simp only [bchar, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_add₀ (hd τ i), show la' τ i + la τ i = 0 from congrFun (congrFun hla τ) i, zpow_zero]
  · rw [he.2.1 y hy b hb]; simp [bchar]
  · rw [← X.χ_add _ _ γ hγ, hla, hχ0 γ hγ]
  · rw [he.2.2 γ hγ y hy, hχ0 γ hγ, one_mul]

theorem mul_mem_cuspOn_of_isSec {Z : Comp Xo c} {G₀ : WTZ E} (h0 : Even G₀.2) {s : Rul Xo c}
    (hs : s ∈ secZ Xo c (exZ Dw G₀)) (hZ : s ∈ suppOn Z)
    (hh : ∀ σ, GoodEmb c σ → ∀ k, ((U σ).X k).IsSec (modelWt (U σ) G₀ k) (rdU (U σ) s k))
    (hb : ∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C)
    {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : f * s ∈ cuspOn U Z (G + G₀) := by
  refine ⟨?_, mul_mem_suppOn _ hZ⟩
  have hf' := mem_cuspW.1 hf.1
  refine mem_cuspW.2 ⟨exZ_add_eq (Dw := Dw) G G₀ ▸ mul_mem_secZ hf'.1 hs, fun σ hσ => ?_⟩
  rw [AllWt.rdU_mul, mem_holSub_model]
  intro k
  rw [modelWt_add (U σ) hG h0 k]
  refine (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_model _ _ _).1 (hf'.2 σ hσ) k) _ ⟨hh σ hσ k, ?_⟩
  obtain ⟨C, hC⟩ := hb σ hσ
  refine ⟨max 0 (C / lieFacZ Dw x G₀), fun y _ => ?_⟩
  by_cases hy : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
  · refine le_max_of_le_right ((le_div_iff₀' (lieFacZ_pos x G₀)).2 ?_)
    have := hC _ hy
    unfold homN ptN at this
    exact this
  · have := rdU_eq_zero (U σ) hZ hy
    simp only at this
    simp [Data.pnorm, this]

theorem exists_twSec_of_dom (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {Z : Comp Xo c} {la : Weight Dw}
    {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ) (hδ : (Function.support δ).Finite)
    {a : (E →+* ℂ) × ℕ → ℕ} (ha : Dom a 0) (hla : exZ Dw (wtOf Dw (-la) 0) = exZ Dw (wtZ a 0)) :
    ∃ t : TwSec U x Z (wtOf Dw la 0), t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo := by
  have hneg : wtOf Dw (-la) 0 + wtOf Dw la 0 = 0 := by rw [← wtOf_add', neg_add_cancel, wtOf_zero]
  have hi : ∀ σ, GoodEmb c σ → ∀ k, ((U σ).X k).IsSec (modelWt (U σ) (wtOf Dw (-la) 0) k) (rdU (U σ) s.inv k) := by
    intro σ hσ k
    rw [modelWt_congr (U σ) hσ (hU σ hσ) hla, modelWt_wtZ]
    refine (hU σ hσ).2.2.2.2.1 a 0 ha _ ?_ k
    rw [← secZ_nat, ← AllWt.exZ_wtZ, ← hla]
    exact s.symm.sig_mem
  have hs : ∀ σ, GoodEmb c σ → ∀ k, ((U σ).X k).IsSec (modelWt (U σ) (wtOf Dw la 0) k) (rdU (U σ) s.sig k) := by
    intro σ hσ k
    have he : ((U σ).X k).IsSec 0 (rdU (U σ) (idem Z) k) := by
      have h1 := (hU σ hσ).2.2.2.2.1 0 0 ⟨fun _ => antitone_const, Even.zero⟩ (idem Z) (by
        rw [← secZ_nat]
        convert idem_mem_secZ Z using 2
        funext i; cases i <;> rfl) k
      convert h1 using 1
      funext τ j; simp [laU]
    refine isSec_inv _ ?_ he (hi σ hσ k) ?_ ?_ ?_ ?_
    · rw [← modelWt_add _ (even_wtOf _ _) (even_wtOf _ _), add_comm, hneg]
      funext τ j; simp [modelWt]
    · exact (congrFun (AllWt.rdU_mul (U σ) _ _) k).symm.trans (by rw [idem_mul_idem])
    · exact (congrFun (AllWt.rdU_mul (U σ) _ _) k).symm.trans (by rw [s.idem_sig])
    · exact (congrFun (AllWt.rdU_mul (U σ) _ _) k).symm.trans (by rw [s.idem_inv])
    · exact (congrFun (AllWt.rdU_mul (U σ) _ _) k).symm.trans (by rw [s.mul_inv])
  have hb : ∀ {la δ} (s : ConstSec U x Z la δ) σ, GoodEmb c σ →
      ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw la 0) s.sig z ≤ C := fun s σ hσ => by
    have h := fun z hz => (s.homN_eq (σ := σ) (z := z) hz).le
    rw [show goodOf c σ = σ from if_pos hσ] at h
    exact ⟨_, h⟩
  refine ⟨TwSec.ofConst s hδ (fun G hG f hf => mul_mem_cuspOn_of_isSec (even_wtOf _ _) s.sig_mem s.sig_mem_suppOn hs
    (hb s) hG hf) (fun G hG f hf => ?_), rfl, rfl, rfl, rfl⟩
  have := mul_mem_cuspOn_of_isSec (even_wtOf (-la) 0) s.symm.sig_mem s.symm.sig_mem_suppOn hi (hb s.symm)
    (hG.add (even_wtOf la 0)) hf
  rwa [add_assoc, add_comm (wtOf Dw la 0), hneg, add_zero] at this

open Classical in

theorem exists_twSec_flat (hq : Dw.q = 0) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {Z : Comp Xo c} {τ : Psi H}
    (s : FlatSec U x Z τ) :
    ∃ t : TwSec U x Z (wtOf Dw (flatWt Dw τ) 0), t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = s.rho_vw ∧ t.hi = t.lo ∧
      t.degLo = s.deg := by
  obtain ⟨t, h1, h2, h3, h4⟩ := exists_twSec_of_dom hU s (finite_flDefect_vw τ)
    (a := fun y => if y.1 = τ.1 then 1 else 0) ⟨fun _ _ _ _ => le_rfl, Even.zero⟩ (by
      funext i
      rcases i with _ | ⟨ρ, i⟩
      · rfl
      · have hi := i.2
        have hρ : ρ (H.rt : E) = H.rt0 := by
          by_contra hn
          simp [Datum.mult, hn, hq] at hi
        refine (wtOf_big (-flatWt Dw τ) 0 ⟨ρ, hρ⟩ i (by simpa [Datum.mult, hρ] using hi)).trans ?_
        simp only [flatWt, parWt, sub_zero, Pi.neg_apply, exZ, wtZ]
        by_cases h1 : ρ = τ.1
        · rw [if_pos h1, if_pos (Subtype.ext h1)]; rfl
        · rw [if_neg h1, if_neg fun h2 => h1 (congrArg Subtype.val h2)]; rfl)
  have h0 : flDefect_vw Dw c τ = 0 := funext fun w => by simp [flDefect_vw, hq]
  replace h3 : t.lo = s.rho_vw := h3.trans ((congrArg (· + s.rho_vw) h0).trans (zero_add _))
  exact ⟨t, h1, h2, h3, h4, by rw [TwSec.degLo, h2, h3]; rfl⟩

theorem exists_unramPts_definite (hq : Dw.q = 0) (hp : 1 ≤ Dw.p) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (hF : FnAlgClosed Xo c) : ∃ B : Finset ℕ, (∀ p ∈ B, p.Prime) ∧ UnramPts Xo c B := by
  classical
  haveI := CompFin.finite_comp Xo c
  choose y₀ h₀ _ using GlobalTheory.FlatLine.DefinitePoint.main E H Dw l Xo c hq hF
  choose S hS0 hS using fun Z => GlobalTheory.FlatLine.exists_finset_integral_of_definite E H Dw l Xo c hq hp hg (y₀ Z)
  have hW : (⋃ Z, ⋃ s ∈ S Z, Function.support fun w : HeightOneSpectrum (𝓞 c.F) => (vAdd w s : ℝ)).Finite :=
    Set.finite_iUnion fun Z => (S Z).finite_toSet.biUnion fun s hs => finite_vAdd (hS0 Z s hs)
  have hch : ∀ w : HeightOneSpectrum (𝓞 c.F), ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 c.F) ∈ w.asIdeal := fun w => by
    haveI := w.isMaximal
    haveI : Finite (𝓞 c.F ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    letI := Ideal.Quotient.field w.asIdeal
    refine ⟨ringChar (𝓞 c.F ⧸ w.asIdeal), CharP.char_is_prime (𝓞 c.F ⧸ w.asIdeal) _, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  choose ch hch₁ hch₂ using hch
  refine ⟨hW.toFinset.image ch, fun p hp => ?_, UnramPts.of_index_one fun Z w hw => ?_⟩
  · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hp
    exact hch₁ w
  · have hn : ∀ s ∈ S Z, vAdd w s = 0 := fun s hs => by
      by_contra h
      refine hw (ch w) (Finset.mem_image_of_mem _ ?_) (hch₂ w)
      simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, Function.mem_support]
      exact ⟨Z, s, hs, by exact_mod_cast h⟩
    obtain ⟨T, io, ho, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F w
    letI := io.toAlgebra
    obtain ⟨z, hz⟩ := GlobalTheory.FlatLine.Definite.exists_bc (Algebra.ofId c.F T.Fr) (y₀ Z)
    have hi := hS Z T io (fun s hs => by rw [ho.2 s]; exact mul_eq_zero_of_right _ (hn s hs)) z hz
    obtain ⟨⟨-, -, -, -, hA, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
    exact ⟨T, io, ⟨z, hA _ _, hi⟩, ho, hfin, liesOn_frMap hz (h₀ Z)⟩

theorem exists_twSec_ne_zero (x : ℝ) : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E)
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q)) (Z : Comp Xo c) (G₀ : WTZ E) (B : Finset ℕ),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) ∧ (∃ i, exZ Dw G₀ i = -1) ∧ (∀ p ∈ B, p.Prime) ∧ UnramPts Xo c B ∧
      ∃ t : TwSec U x Z G₀, IntOff B t.lo ∧ t.hi = t.lo := by
  obtain ⟨D, hp, hq⟩ := GlobalTheory.CM.CyclotomicTwentyEight.exists_datum
  have hpq : 1 ≤ D.p + D.q := by omega
  obtain ⟨l, -, hg, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx _ GlobalTheory.CM.CyclotomicTwentyEight.host 1 one_pos
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ D l hpq
  obtain ⟨c₀⟩ : Nonempty (Coeff l) := inferInstance
  obtain ⟨-, c, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c₀ hpq
  obtain ⟨⟨Z⟩, -⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c hpq
  have hU : ∀ σ : c.F →+* ℂ, ∃ U : Unf Xo c σ (D.p + D.q), GoodEmb c σ → IsUnf U := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, hU⟩ := GlobalTheory.IsUnfEx.exists_isUnf GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.QNorm.hasseNormSt
        GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.abelianSchemeLaws_all.2.secTwist _ _ D l Xo c σ hpq hσ
      exact ⟨U.toPj, fun _ => hU⟩
    · exact ⟨{ Comp := PEmpty, X := fun k => k.elim, un := fun k => k.elim }, fun h => absurd h hσ⟩
  choose U hU using hU
  obtain ⟨τ⟩ : Nonempty (Psi GlobalTheory.CM.CyclotomicTwentyEight.host) := by
    obtain ⟨ρ⟩ : Nonempty (GlobalTheory.CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight →+* ℂ) := inferInstance
    by_cases h : ρ (GlobalTheory.CM.CyclotomicTwentyEight.host.rt : GlobalTheory.CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight) = GlobalTheory.CM.CyclotomicTwentyEight.host.rt0
    exacts [⟨⟨ρ, h⟩⟩, ⟨⟨_, conj_mem h⟩⟩]
  obtain ⟨s⟩ := GlobalTheory.FlatLine.Definite.nonempty_flatSec U x hq hp.ge hg hU (hc c le_rfl) Z τ
  obtain ⟨t, h1, -, h3, h4, -⟩ := exists_twSec_flat hq hU s
  obtain ⟨B, hB, hun⟩ := exists_unramPts_definite (Xo := Xo) (c := c) hq hp.ge hg (hc c le_rfl)
  refine ⟨_, _, _, _, _, D, l, Xo, c, U, Z, _, B, hU, ⟨some ⟨τ.1, ⟨0, ?_⟩⟩, ?_⟩, hB, hun, t, fun w hw => ?_, h4⟩
  · rw [Datum.mult, if_pos τ.2]; omega
  · refine (wtOf_big (flatWt D τ) 0 τ 0 (by omega)).trans ?_
    simp [flatWt, parWt]
  · obtain ⟨v, hv, hi⟩ := hun Z w hw
    obtain ⟨b, hb, -, h5, h6⟩ := t.exists_val hv
    rw [h4] at h6
    rcases hi t.sig with h | ⟨n, h⟩
    · exact absurd (hb.symm.trans h) (EReal.coe_ne_top b)
    · exact ⟨n, (le_antisymm h5 h6).trans (EReal.coe_eq_coe_iff.1 (hb.symm.trans h))⟩

theorem TwSec.degLo_symm {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) (h : s.hi = s.lo) :
    s.symm.degLo = -s.degLo := by
  show lineDeg s.cInf⁻¹ (-s.hi) = _
  rw [h, lineDeg_inv]; rfl

end GlobalTheory.FlatTw

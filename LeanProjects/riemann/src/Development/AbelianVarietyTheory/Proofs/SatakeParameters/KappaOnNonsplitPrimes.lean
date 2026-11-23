import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.DetMemOfEntries
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NormLeOneOfRoot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOneOfTrace

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv stdLat stdH relIdx imgLat pow4 StdData alphaQ IsSelfDual)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.L2.Th1.F (cmTheta)

namespace GlobalTheory.ThLoc.KapNonSplit

theorem norm_add_of_lt {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] {x y : E} (h : ‖y‖ < ‖x‖) :
    ‖x + y‖ = ‖x‖ := by
  apply le_antisymm
  · exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le le_rfl h.le)
  · have h1 := IsUltrametricDist.norm_add_le_max (x + y) (-y)
    rw [add_neg_cancel_right, norm_neg] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)

theorem one_le_norm (l : ℕ) [Fact l.Prime] (d : ℕ) (hj : jacobiSym (-(d : ℤ)) l = -1) (w : ℚ_[l]) :
    1 ≤ ‖(1 : ℚ_[l]) + (d : ℚ_[l]) * w ^ 2‖ := by
  have hleg : legendreSym l (-(d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have hdz : ((d : ℕ) : ZMod l) ≠ 0 := by
    intro h0
    have h1 : legendreSym l (-(d : ℤ)) = 0 := by
      rw [legendreSym.eq_zero_iff]; push_cast; rw [h0, neg_zero]
    rw [h1] at hleg; norm_num at hleg
  have hnd : ¬ l ∣ d := fun h => hdz ((ZMod.natCast_eq_zero_iff d l).2 h)
  have hd1 : ‖(d : ℚ_[l])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd)
  by_contra hlt
  push Not at hlt
  rcases lt_trichotomy ‖w‖ 1 with h | h | h
  · have h2 : ‖(d : ℚ_[l]) * w ^ 2‖ < ‖(1 : ℚ_[l])‖ := by
      rw [norm_mul, norm_pow, hd1, one_mul, norm_one]; nlinarith [norm_nonneg w]
    rw [norm_add_of_lt h2, norm_one] at hlt
    exact lt_irrefl _ hlt
  · let W : ℤ_[l] := ⟨w, h.le⟩
    have hZ : ‖(1 : ℤ_[l]) + (d : ℤ_[l]) * W ^ 2‖ < 1 := by
      rw [PadicInt.norm_def]
      push_cast
      exact hlt
    have hmem : (1 : ℤ_[l]) + (d : ℤ_[l]) * W ^ 2 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hZ
    rw [RingHom.mem_ker, map_add, map_one, map_mul, map_pow, map_natCast] at hmem
    set z := PadicInt.toZMod W with hzdef
    have hz : z ≠ 0 := by
      intro h0
      rw [h0] at hmem
      simp at hmem
    have h0 : ((-(d : ℤ) : ℤ) : ZMod l) ≠ 0 := by push_cast; exact neg_ne_zero.2 hdz
    have hsq : IsSquare ((-(d : ℤ) : ℤ) : ZMod l) := by
      refine ⟨z⁻¹, ?_⟩
      push_cast
      field_simp
      linear_combination (-1 : ZMod l) * hmem
    have h3 := (legendreSym.eq_one_iff l h0).2 hsq
    rw [h3] at hleg
    norm_num at hleg
  · have h2 : ‖(1 : ℚ_[l])‖ < ‖(d : ℚ_[l]) * w ^ 2‖ := by
      rw [norm_mul, norm_pow, hd1, one_mul, norm_one]; nlinarith [norm_nonneg w]
    rw [add_comm, norm_add_of_lt h2, norm_mul, norm_pow, hd1, one_mul] at hlt
    nlinarith [norm_nonneg w]

theorem norm_four_le (l : ℕ) [Fact l.Prime] : ‖(4 : ℚ_[l])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := l) 4
  simpa using this

theorem trace_le_inert (l : ℕ) [Fact l.Prime] (d : ℕ) (hj : jacobiSym (-(d : ℤ)) l = -1) (T v : ℚ_[l])
    (h : T ^ 2 + (d : ℚ_[l]) * v ^ 2 = 4) : ‖T‖ ≤ 1 := by
  by_contra hbig
  push Not at hbig
  have hT0 : T ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hbig
    linarith
  have key := one_le_norm l d hj (v / T)
  have e : (1 : ℚ_[l]) + (d : ℚ_[l]) * (v / T) ^ 2 = 4 / T ^ 2 := by
    field_simp
    linear_combination h
  rw [e, norm_div, norm_pow] at key
  have hpos : 0 < ‖T‖ ^ 2 := by positivity
  have : ‖(4 : ℚ_[l])‖ / ‖T‖ ^ 2 < 1 := by
    rw [div_lt_one hpos]
    nlinarith [norm_four_le l]
  linarith

theorem trace_le_ramified (l : ℕ) [Fact l.Prime] (T v : ℚ_[l])
    (h : T ^ 2 + (l : ℚ_[l]) * v ^ 2 = 4) : ‖T‖ ≤ 1 := by
  by_contra hbig
  push Not at hbig
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hT0 : T ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hbig
    linarith
  have hT2 : 1 < ‖T ^ 2‖ := by
    rw [norm_pow]; nlinarith
  have h4 : ‖(-4 : ℚ_[l])‖ < ‖T ^ 2‖ := by
    rw [norm_neg]; exact (norm_four_le l).trans_lt hT2
  have e : (l : ℚ_[l]) * v ^ 2 = -(T ^ 2 + (-4)) := by linear_combination h
  have hn : ‖(l : ℚ_[l]) * v ^ 2‖ = ‖T ^ 2‖ := by
    rw [e, norm_neg, norm_add_of_lt h4]
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hn
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, norm_zero] at hn
    rw [← hn] at hT2
    linarith
  rw [norm_mul, norm_pow, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hT0,
    Padic.norm_eq_zpow_neg_valuation hv0] at hn
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have e1 : (l : ℝ)⁻¹ * ((l : ℝ) ^ (-v.valuation)) ^ 2 = (l : ℝ) ^ (-1 - 2 * v.valuation) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_neg_one, ← zpow_add₀ hl0]
    congr 1
    push_cast
    ring
  have e2 : ((l : ℝ) ^ (-T.valuation)) ^ 2 = (l : ℝ) ^ (-2 * T.valuation) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [e1, e2] at hn
  have := zpow_right_injective₀ (by positivity : (0 : ℝ) < l) hl1.ne' hn
  omega

theorem norm_of_normOne {a : ℕ} {b c : ℤ} {d : ℕ} (hok : PI.UnitDetRootDefs.CmOK a b c d) (l : ℕ) [Fact l.Prime]
    (hT : ∀ T v : ℚ_[l], T ^ 2 + (d : ℚ_[l]) * v ^ 2 = 4 → ‖T‖ ≤ 1) (ι : ℂ ≃+* ℂ_[l]) {x : ℂ}
    (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) (h1 : x * conj x = 1) : ‖ι x‖ = 1 := by
  first
  | exact @_root_.GlobalTheory.TraceNormCoordinates.norm_eq_one
  | exact _root_.GlobalTheory.TraceNormCoordinates.norm_eq_one
  | (apply _root_.GlobalTheory.TraceNormCoordinates.norm_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceNormCoordinates.norm_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceNormCoordinates.norm_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceNormCoordinates.norm_eq_one ..)

theorem le_one (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (z : ℂ) (hz : IsIntegral ℤ z) : ‖ι z‖ ≤ 1 := by
  obtain ⟨p, hp, hpz⟩ := hz
  apply PI.UnitaryGroupMassFormula.UnitDetRoot.norm_le_one_of_root p hp
  have h : (ι.toRingHom) (p.eval₂ (algebraMap ℤ ℂ) z) = 0 := by rw [hpz, map_zero]
  rw [Polynomial.hom_eval₂, RingHom.ext_int (ι.toRingHom.comp (algebraMap ℤ ℂ)) (Int.castRingHom _)] at h
  exact h

theorem norm_unit (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (k : ℕ) (hk : ¬ l ∣ k) {x w : ℂ} (hx : IsIntegral ℤ x)
    (hw : IsIntegral ℤ w) (hm : (k : ℂ) = x * w) : ‖ι x‖ = 1 := by
  have e1 := le_one l ι x hx
  have e2 := le_one l ι w hw
  have e3 : ‖ι x‖ * ‖ι w‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← hm, PI.UnitaryGroupMassFormula.UnitDetRoot.norm_iota_natCast l ι k hk]
  refine le_antisymm e1 ?_
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι w)]

theorem norm_rt {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (p : ℕ)
    (hp : p.Prime) (hs : SplitK D p) (hpl : p ≠ l) : ‖ι (k.rt p)‖ = 1 := by
  have hh := k.rt_pow p hp hs
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 D.host.K, w * k.pi p = (p : 𝓞 D.host.K) ^ classNumber D.host.K := by
    have hmem : (p : 𝓞 D.host.K) ^ classNumber D.host.K ∈ (k.pp p).asIdeal ^ classNumber D.host.K :=
      Ideal.pow_mem_pow (k.pp_over p hp hs) _
    rw [k.pi_gen p hp hs, Ideal.mem_span_singleton'] at hmem
    exact hmem
  have hpl' : ¬ l ∣ p ^ classNumber D.host.K := by
    intro h
    have h1 : l ∣ p := (Fact.out : l.Prime).dvd_of_dvd_pow h
    exact hpl (((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h1).symm)
  have hwK : (w : D.host.K) * (k.pi p : D.host.K) = ((p ^ classNumber D.host.K : ℕ) : D.host.K) := by
    have := congrArg (algebraMap (𝓞 D.host.K) D.host.K) hw
    simpa using this
  let fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  let fK' : D.host.K →+* ℂ := D.host.φ₀.comp ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E))
  have hint : ∀ (g : D.host.K →+* ℂ) (x : 𝓞 D.host.K), IsIntegral ℤ (g (x : D.host.K)) := fun g x =>
    map_isIntegral_int g (NumberField.RingOfIntegers.isIntegral_coe x)
  have e : ∀ g : D.host.K →+* ℂ, ((p ^ classNumber D.host.K : ℕ) : ℂ) = g (k.pi p : D.host.K) * g (w : D.host.K) := by
    intro g
    rw [← map_natCast g, ← hwK, map_mul, mul_comm]
  have h1 : ‖ι (D.host.φ₀ (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))‖ = 1 :=
    norm_unit l ι _ hpl' (hint fK (k.pi p)) (hint fK w) (e fK)
  have h2 : ‖ι (D.host.φ₀ (D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)))‖ = 1 :=
    norm_unit l ι _ hpl' (hint fK' (k.pi p)) (hint fK' w) (e fK')
  have hpow : ‖ι (k.rt p)‖ ^ (2 * classNumber D.host.K) = 1 := by
    rw [← norm_pow, ← map_pow, hh, map_div₀, norm_div, h1, h2, div_one]
  have hc := NumberField.classNumber_pos D.host.K
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 hpow

theorem norm_kappa {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (l : ℕ) [Fact l.Prime]
    (hl : ∀ p : ℕ, p.Prime → SplitK D p → p ≠ l) (ι : ℂ ≃+* ℂ_[l]) : ‖ι B.kappa‖ = 1 := by
  show ‖ι (∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, B.kc.rt p ^ (-(B.kc.yP p)))‖ = 1
  refine finprod_induction (fun z => ‖ι z‖ = 1) (by simp) (fun x y hx hy => ?_) (fun p => ?_)
  · simp only [map_mul, norm_mul, hx, hy, one_mul]
  · simp only [map_zpow₀, norm_zpow]
    rw [norm_rt B.kc l ι p.1 p.2.1 p.2.2 (hl p.1 p.2.1 p.2.2), one_zpow]

theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem odd_of_cmOK {a : ℕ} {b c : ℤ} {d : ℕ} (h : CmOK a b c d) : Odd b := by
  by_contra hb
  obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.1 hb
  have h1 := h.1
  have h8 := h.2.2.1
  have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
    have : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [this] at h1
    linarith
  generalize (a : ℤ) * c - k * k = t at h2
  omega

theorem stable_latA {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (b : ℤ) (hb : Odd b) :
    ∀ x ∈ B.latA, cmTheta b D.host.d • x ∈ B.latA := by
  have hM : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
    refine stable_of_one _ _ (fun x hx => ?_) b hb
    have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.lamMM_smul (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR.om D) hx
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.theta_eq] at this
    exact this
  rintro x ⟨x', hx', rfl⟩
  refine ⟨cmTheta b D.host.d • x', fun a' => hM _ (hx' a'), ?_⟩
  simp

theorem trace_le (D : D7) (l : ℕ) [Fact l.Prime] (hns : ¬ SplitK D l) (T v : ℚ_[l])
    (h : T ^ 2 + (D.host.d : ℚ_[l]) * v ^ 2 = 4) : ‖T‖ ≤ 1 := by
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hl2 : l ≠ 2 := fun h2 => hns (Or.inl h2)
  have hj1 : jacobiSym (-(D.host.d : ℤ)) l ≠ 1 := fun h1 => hns (Or.inr h1)
  by_cases hdvd : l ∣ D.host.d
  · have e : l = D.host.d := (Nat.prime_dvd_prime_iff_eq Fact.out hdp).1 hdvd
    rw [← e] at h
    exact trace_le_ramified l T v h
  · have hz : ((-(D.host.d : ℤ) : ℤ) : ZMod l) ≠ 0 := by
      push_cast
      exact neg_ne_zero.2 fun h0 => hdvd ((ZMod.natCast_eq_zero_iff _ l).1 h0)
    have hj : jacobiSym (-(D.host.d : ℤ)) l = -1 := by
      rcases legendreSym.eq_one_or_neg_one l hz with h1 | h1
      · rw [jacobiSym.legendreSym.to_jacobiSym] at h1
        exact absurd h1 hj1
      · rw [jacobiSym.legendreSym.to_jacobiSym] at h1
        exact h1
    exact trace_le_inert l _ hj T v h

end GlobalTheory.ThLoc.KapNonSplit

open GlobalTheory.ThLoc.KapNonSplit in

theorem GlobalTheory.ThLoc.kappaNonSplit : ∀ D : D7, KappaOn (fun D p => ¬ SplitK D p) D := by
  intro D cc δ B hcc hδ l _ ι hns u hiso j1 _ j2
  have hnotl : ∀ p : ℕ, p.Prime → SplitK D p → p ≠ l := by
    intro p _ hs hpl
    subst hpl
    exact hns hs
  rw [norm_kappa B l hnotl ι, one_pow, one_mul]
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd : 0 < D.host.d := hdp.pos
  have hd8 : D.host.d % 8 = 7 := by
    have := D.host.hyp.2.2.2.1
    omega
  obtain ⟨a₀, b₀, c₀, ha, lam, hlam, hcm, hL⟩ := KS.exists_cmOK D.host.d hd hd8 hdp B.L (GlobalTheory.FourthRootStd.hst B)
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd : IsSelfDual (stdH B.L (Fin 4 × D.what₂.Tau)) B.latA := hS.selfDual
  have i1 : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) B.latA ≠ 0 := hS.idx₁
  have i2 : relIdx B.latA (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 := hS.idx₂
  have hsta := stable_latA B b₀ (odd_of_cmOK hcm)
  have eH := KS.stdH_congr hL.symm (Fin 4 × D.what₂.Tau)
  have eS : stdLat B.L (Fin 4 × D.what₂.Tau) = stdLat (cmL a₀ b₀ D.host.d ha hd lam hlam) (Fin 4 × D.what₂.Tau) := by
    unfold Formalism.L2.Th1.H.stdLat
    rw [hL]
  rw [eH] at hiso hsd
  rw [eS] at j1 j2 i1 i2
  obtain ⟨hmem, hone⟩ := PI.UnitaryGroupMassFormula.UnitDetRoot.detInK a₀ b₀ c₀ D.host.d ha hd lam hlam (Fin 4 × D.what₂.Tau) B.latA
    ⟨hcm, hsd, hsta, i1, i2⟩ u ⟨hiso, j1, j2⟩
  exact norm_of_normOne hcm l (trace_le D l hns) ι hmem hone

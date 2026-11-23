import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.VIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSysW

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp)

namespace TransW

section Sim

variable {K : Type} [NormedField K]

def Sim (f g : K⟦X⟧) : Prop := ∃ ρ : K, ‖ρ‖ = 1 ∧ f = C ρ * g

theorem Sim.refl (f : K⟦X⟧) : Sim f f := ⟨1, norm_one, by simp⟩

theorem Sim.symm {f g : K⟦X⟧} (h : Sim f g) : Sim g f := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  have hne : ρ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hρ
    exact zero_ne_one hρ
  refine ⟨ρ⁻¹, by rw [norm_inv, hρ, inv_one], ?_⟩
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]

theorem Sim.trans {f g h : K⟦X⟧} (h1 : Sim f g) (h2 : Sim g h) : Sim f h := by
  obtain ⟨ρ, hρ, rfl⟩ := h1
  obtain ⟨σ, hσ, rfl⟩ := h2
  exact ⟨ρ * σ, by rw [norm_mul, hρ, hσ, one_mul], by rw [map_mul, mul_assoc]⟩

theorem Sim.mul {f g f' g' : K⟦X⟧} (h1 : Sim f g) (h2 : Sim f' g') : Sim (f * f') (g * g') := by
  obtain ⟨ρ, hρ, rfl⟩ := h1
  obtain ⟨σ, hσ, rfl⟩ := h2
  exact ⟨ρ * σ, by rw [norm_mul, hρ, hσ, one_mul], by rw [map_mul]; ring⟩

theorem Sim.mul_left (a : K⟦X⟧) {f g : K⟦X⟧} (h : Sim f g) : Sim (a * f) (a * g) := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  exact ⟨ρ, hρ, by ring⟩

theorem Sim.sq {f g : K⟦X⟧} (h : Sim f g) : Sim (f ^ 2) (g ^ 2) := by
  rw [pow_two, pow_two]
  exact h.mul h

theorem Sim.gaussOne {f g : K⟦X⟧} (h : Sim f g) (hg : GaussOne g) : GaussOne f := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  unfold GaussOne IntS at *
  obtain ⟨hI, n, hn⟩ := hg
  refine ⟨fun m => ?_, n, ?_⟩
  · rw [PowerSeries.coeff_C_mul, norm_mul, hρ, one_mul]
    exact hI m
  · rw [PowerSeries.coeff_C_mul, norm_mul, hρ, one_mul, hn]

theorem gaussOne_of_oneUnit {f : K⟦X⟧} (h : OneUnit f) : GaussOne f := by
  unfold OneUnit at h
  unfold GaussOne
  refine ⟨h.2, 0, ?_⟩
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h.1, norm_one]

theorem gaussOne_of_shape {f : K⟦X⟧} {a : K} (ha : ‖a‖ = 1) (h : OneUnit (C a⁻¹ * f)) : GaussOne f := by
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ha
    exact zero_ne_one ha
  refine Sim.gaussOne ⟨a, ha, ?_⟩ (gaussOne_of_oneUnit h)
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul]

end Sim

section An

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l])

theorem norm_root {ζ : ℂ} {m : ℕ} (hm : 0 < m) (h : ζ ^ m = 1) : ‖ι ζ‖ = 1 := by
  have h1 : ‖ι ζ‖ ^ m = 1 := by
    rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h1

private theorem iteratedDeriv_const_mul_fun (a : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => a * f z) = fun z => a * iteratedDeriv n f z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
    exact deriv_const_mul_field' a

theorem inW_const_mul (a : ℂ) (f : ℂ → ℂ) :
    inW l ι W (fun z => a * f z) = C (ι a) * inW l ι W f := by
  have ht : Formalism.L2.Th1.F.taylor0 (fun z => a * f z) = C a * Formalism.L2.Th1.F.taylor0 f := by
    ext n
    simp [Formalism.L2.Th1.F.taylor0, iteratedDeriv_const_mul_fun, mul_div_assoc]
  have hs : PowerSeries.HasSubst (Formalism.L2.Th1.A.logSer W) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      have h0 : PowerSeries.coeff 0 (Formalism.L2.Th1.A.logSer W) = 0 := by
        simp [Formalism.L2.Th1.A.logSer, Formalism.L2.Th1.A.integ]
      first
        | exact (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm.trans h0
        | exact h0
        | simpa using h0
        | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact h0))
  unfold inW
  rw [ht, map_mul, PowerSeries.map_C, ← PowerSeries.smul_eq_C_mul, ← PowerSeries.smul_eq_C_mul,
    PowerSeries.subst_smul hs]
  rfl

open Classical in

def piW (hA : PtWAdd) (hU : Unif l L ι W) : ℂ →+ W.toAffine.Point :=
  AddMonoidHom.mk' (ptW l L ι W) (hA l L ι W hU)

variable {l L ι W}

open Classical in
theorem nsmul_ptW (hA : PtWAdd) (hU : Unif l L ι W) (t : ℂ) (N : ℕ) :
    N • ptW l L ι W t = ptW l L ι W ((N : ℂ) * t) := by
  have h := map_nsmul (piW l L ι W hA hU) N t
  simpa [piW, nsmul_eq_mul] using h.symm

open Classical in
theorem zsmul_ptW (hA : PtWAdd) (hU : Unif l L ι W) (t : ℂ) (k : ℤ) :
    k • ptW l L ι W t = ptW l L ι W ((k : ℂ) * t) := by
  have h := map_zsmul (piW l L ι W hA hU) k t
  simpa [piW, zsmul_eq_mul] using h.symm

open Classical in
theorem sub_ptW (hA : PtWAdd) (hU : Unif l L ι W) (s t : ℂ) :
    ptW l L ι W (s - t) = ptW l L ι W s - ptW l L ι W t := by
  have h := map_sub (piW l L ι W hA hU) s t
  simpa [piW] using h

open Classical in

theorem ptW_int (hA : PtWAdd) (hZ : PtWZero) (hU : Unif l L ι W) (hW : IntCurve W) (t : ℂ) (N : ℕ)
    (hlN : ¬ l ∣ N) (hNt : (N : ℂ) * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    ‖px W (ptW l L ι W t)‖ ≤ 1 ∧ ‖py W (ptW l L ι W t)‖ ≤ 1 :=
  torsionIntegral ℂ_[l] W hW _ N (Tor.norm_natCast l hlN)
    (by rw [nsmul_ptW hA hU]; exact (hZ l L ι W hU _).2 hNt)
    (fun h => ht ((hZ l L ι W hU t).1 h))

open Classical in

theorem restrict (hS : AnalyticSysW) (hA : PtWAdd) (hZ : PtWZero) (hU : Unif l L ι W)
    (hW : IntCurve W) (t : ℂ) (N : ℕ) (hlN : ¬ l ∣ N) (hNt : (N : ℂ) * t ∈ L.lattice) :
    IntPts W ((piW l L ι W hA hU).comp (AddSubgroup.zmultiples t).subtype) ∧
    IsTransSys W ((piW l L ι W hA hU).comp (AddSubgroup.zmultiples t).subtype)
      (fun s : AddSubgroup.zmultiples t => gW l L ι W (s : ℂ)) := by
  constructor
  · rintro ⟨s, hs⟩ h0
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hs
    refine ptW_int hA hZ hU hW _ N hlN ?_ (fun hmem => h0 ((hZ l L ι W hU _).2 hmem))
    have e : (N : ℂ) * (k • t) = (k : ℂ) * ((N : ℂ) * t) := by
      rw [zsmul_eq_mul]
      ring
    change (N : ℂ) * (k • t) ∈ L.lattice
    rw [e]
    exact Tor.int_mul_mem L k hNt
  · obtain ⟨h1, h2, h3⟩ := hS l L ι W hU (piW l L ι W hA hU) (fun _ => rfl)
    exact ⟨fun s => h1 s, fun s => h2 s, fun P Q => h3 P Q⟩

open Classical in
theorem gW_gauss (hS : AnalyticSysW) (hA : PtWAdd) (hZ : PtWZero) (hU : Unif l L ι W)
    (hW : IntCurve W) (t : ℂ) (N : ℕ) (hlN : ¬ l ∣ N) (hNt : (N : ℂ) * t ∈ L.lattice) :
    GaussOne (gW l L ι W t) := by
  obtain ⟨hIP, hTS⟩ := restrict hS hA hZ hU hW t N hlN hNt
  exact transGauss ℂ_[l] W hW (AddSubgroup.zmultiples t) _ _ hIP hTS
    ⟨t, AddSubgroup.mem_zmultiples t⟩ N (Tor.norm_natCast l hlN)
    (by
      change N • ptW l L ι W t = 0
      rw [nsmul_ptW hA hU]
      exact (hZ l L ι W hU _).2 hNt)

variable (l L ι W)

def eW (t : ℂ) : PowerSeries ℂ_[l] := inW l ι W (opU L t (sgStar L))

def hW (t₀ t : ℂ) : PowerSeries ℂ_[l] := inW l ι W (opU L t (th0 L t₀))

theorem gW_eq (t : ℂ) : gW l L ι W t = fExp (phW l L ι W) * eW l L ι W t := rfl

theorem eW_eq (t : ℂ) : eW l L ι W t = fExp (-(phW l L ι W)) * gW l L ι W t := by
  rw [gW_eq, ← mul_assoc, mul_comm (fExp (-(phW l L ι W))),
    AnaSysW.fExp_cancel (l := l) (L := L) (ι := ι) (W := W), one_mul]

theorem hW_sim (t₀ t : ℂ) (M : ℕ) (hM : 0 < M) (ht : (M : ℂ) * t ∈ L.lattice)
    (h0 : (M : ℂ) * t₀ ∈ L.lattice) (h0' : t₀ ∉ L.lattice) :
    Sim (hW l L ι W t₀ t) (C (ι (opU L t₀ (sgStar L) 0))⁻¹ * eW l L ι W (t + t₀)) := by
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L ((M : ℂ) * t) ((M : ℂ) * t₀) ht h0
  have hh : Formalism.L2.Th1.F.herm L ((M : ℂ) * t) ((M : ℂ) * t₀)
      = (((M : ℝ) ^ 2 : ℝ) : ℂ) * Formalism.L2.Th1.F.herm L t t₀ := by
    unfold Formalism.L2.Th1.F.herm
    simp only [map_mul, map_natCast]
    push_cast
    ring
  have halt : (M : ℝ) ^ 2 * Formalism.L2.Th1.F.altE L t t₀ = k := by
    rw [← hk]
    unfold Formalism.L2.Th1.F.altE
    rw [hh, Complex.im_ofReal_mul]
  have halt' : (M : ℂ) ^ 2 * (Formalism.L2.Th1.F.altE L t t₀ : ℂ) = (k : ℂ) := by
    exact_mod_cast halt
  have he : Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L t t₀ : ℂ)) ^ (2 * M ^ 2)
      = 1 := by
    rw [← Complex.exp_nat_mul]
    have h2 : ((2 * M ^ 2 : ℕ) : ℂ) * (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L t t₀ : ℂ))
        = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * halt'
    rw [h2, Complex.exp_int_mul_two_pi_mul_I]
  have hc : ((Formalism.L2.Th1.F.altE L t t₀ : ℝ) : ℂ) * Complex.I
      = (Formalism.L2.Th1.F.herm L t t₀ - (starRingEnd ℂ) (Formalism.L2.Th1.F.herm L t t₀)) / 2 := by
    rw [Complex.sub_conj]
    unfold Formalism.L2.Th1.F.altE
    push_cast
    ring
  have hcj : (starRingEnd ℂ) (Formalism.L2.Th1.F.herm L t t₀) = Formalism.L2.Th1.F.herm L t₀ t := by
    simp only [Formalism.L2.Th1.F.herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have hop : opU L t (th0 L t₀) = fun z => (opU L t₀ (sgStar L) 0)⁻¹ *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L t t₀ : ℂ)) *
      opU L (t + t₀) (sgStar L) z := by
    funext z
    have key : Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L (z + t) t₀
          - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t₀ t₀ / 2)
        * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z t
          - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t t / 2)
        = Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L t t₀ : ℂ))
          * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z (t + t₀)
            - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L (t + t₀) (t + t₀) / 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [show -(Real.pi : ℂ) * Complex.I * ((Formalism.L2.Th1.F.altE L t t₀ : ℝ) : ℂ)
          = -(Real.pi : ℂ) * (((Formalism.L2.Th1.F.altE L t t₀ : ℝ) : ℂ) * Complex.I) by ring, hc, hcj]
      simp only [Formalism.L2.Th1.F.herm, map_add]
      ring
    have hth : th0 L t₀ (z + t) = opU L t₀ (sgStar L) (z + t) * (opU L t₀ (sgStar L) 0)⁻¹ := by
      unfold th0
      exact div_eq_mul_inv _ _
    have hL : opU L t (th0 L t₀) z = th0 L t₀ (z + t) * Complex.exp (-(Real.pi : ℂ) *
        Formalism.L2.Th1.F.herm L z t - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t t / 2) := rfl
    rw [hL, hth]
    generalize (opU L t₀ (sgStar L) 0)⁻¹ = D
    simp only [opU]
    rw [show z + t + t₀ = z + (t + t₀) by ring]
    linear_combination (D * sgStar L (z + (t + t₀))) * key
  refine ⟨ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L t t₀ : ℂ))),
    norm_root (l := l) (ι := ι) (by positivity) he, ?_⟩
  unfold hW eW
  rw [hop, inW_const_mul]
  simp only [map_mul, map_inv₀]
  ring

theorem opU_add_lattice (t ω : ℂ) (hω : ω ∈ L.lattice) :
    opU L (t + ω) (sgStar L) = fun z =>
      ((Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L t ω : ℂ)))⁻¹ *
        Formalism.L2.Th1.F.semiChar L ω) * opU L t (sgStar L) z := by
  funext z
  have hq := Formalism.L2.Th1.F.sgStarQuasi L ω (z + t) hω
  have hc : ((Formalism.L2.Th1.F.altE L t ω : ℝ) : ℂ) * Complex.I
      = (Formalism.L2.Th1.F.herm L t ω - (starRingEnd ℂ) (Formalism.L2.Th1.F.herm L t ω)) / 2 := by
    rw [Complex.sub_conj]
    unfold Formalism.L2.Th1.F.altE
    push_cast
    ring
  have hcj : (starRingEnd ℂ) (Formalism.L2.Th1.F.herm L t ω) = Formalism.L2.Th1.F.herm L ω t := by
    simp only [Formalism.L2.Th1.F.herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have key : Complex.exp ((Real.pi : ℂ) * Formalism.L2.Th1.F.herm L (z + t) ω
        + (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2)
      * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z (t + ω)
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L (t + ω) (t + ω) / 2)
      = (Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L t ω : ℂ)))⁻¹
        * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z t
          - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t t / 2) := by
    rw [← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [show -(-(Real.pi : ℂ) * Complex.I * ((Formalism.L2.Th1.F.altE L t ω : ℝ) : ℂ))
        = (Real.pi : ℂ) * (((Formalism.L2.Th1.F.altE L t ω : ℝ) : ℂ) * Complex.I) by ring, hc, hcj]
    simp only [Formalism.L2.Th1.F.herm, map_add]
    ring
  simp only [opU]
  rw [show z + (t + ω) = z + t + ω by ring, hq]
  linear_combination (Formalism.L2.Th1.F.semiChar L ω * sgStar L (z + t)) * key

theorem eW_sim (a b : ℂ) (M : ℕ) (hM : 0 < M) (hb : (M : ℂ) * b ∈ L.lattice)
    (hab : a - b ∈ L.lattice) : Sim (eW l L ι W a) (eW l L ι W b) := by
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L ((M : ℂ) * b) (a - b) hb hab
  have hh : Formalism.L2.Th1.F.herm L ((M : ℂ) * b) (a - b)
      = ((M : ℝ) : ℂ) * Formalism.L2.Th1.F.herm L b (a - b) := by
    unfold Formalism.L2.Th1.F.herm
    push_cast
    ring
  have halt : (M : ℝ) * Formalism.L2.Th1.F.altE L b (a - b) = k := by
    rw [← hk]
    unfold Formalism.L2.Th1.F.altE
    rw [hh, Complex.im_ofReal_mul]
  have halt' : (M : ℂ) * (Formalism.L2.Th1.F.altE L b (a - b) : ℂ) = (k : ℂ) := by
    exact_mod_cast halt
  set c := (Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L b (a - b) : ℂ)))⁻¹ *
    Formalism.L2.Th1.F.semiChar L (a - b) with hc
  have hs2 : Formalism.L2.Th1.F.semiChar L (a - b) ^ 2 = 1 := by
    unfold Formalism.L2.Th1.F.semiChar
    split_ifs <;> norm_num
  have he : Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L b (a - b) : ℂ)) ^ (2 * M)
      = 1 := by
    rw [← Complex.exp_nat_mul]
    have h2 : ((2 * M : ℕ) : ℂ) * (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L b (a - b) : ℂ))
        = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * halt'
    rw [h2, Complex.exp_int_mul_two_pi_mul_I]
  have hc1 : c ^ (2 * M) = 1 := by
    rw [hc, mul_pow, inv_pow, he, inv_one, one_mul, pow_mul, hs2, one_pow]
  have hop : opU L a (sgStar L) = fun z => c * opU L b (sgStar L) z := by
    have h := opU_add_lattice L b (a - b) hab
    rw [show b + (a - b) = a by ring] at h
    exact h
  refine ⟨ι c, norm_root (l := l) (ι := ι) (by positivity) hc1, ?_⟩
  unfold eW
  rw [hop, inW_const_mul]

theorem hW_sim_hW (t₀ a b : ℂ) (M : ℕ) (hM : 0 < M) (ha : (M : ℂ) * a ∈ L.lattice)
    (hb : (M : ℂ) * b ∈ L.lattice) (h0 : (M : ℂ) * t₀ ∈ L.lattice) (h0' : t₀ ∉ L.lattice)
    (hab : a - b ∈ L.lattice) : Sim (hW l L ι W t₀ a) (hW l L ι W t₀ b) := by
  have h1 := hW_sim l L ι W t₀ a M hM ha h0 h0'
  have h2 := hW_sim l L ι W t₀ b M hM hb h0 h0'
  have h3 := eW_sim l L ι W (a + t₀) (b + t₀) M hM
    (by rw [mul_add]; exact add_mem hb h0)
    (by rw [show a + t₀ - (b + t₀) = a - b by ring]; exact hab)
  exact h1.trans ((Sim.mul_left _ h3).trans h2.symm)

variable {l L ι W}

open Classical in

theorem eW_prod (hS : AnalyticSysW) (hA : PtWAdd) (hU : Unif l L ι W) (P Q : ℂ) (hP : P ∉ L.lattice)
    (hQ : ptW l L ι W Q ≠ 0) :
    eW l L ι W (P + Q) * eW l L ι W (P - Q) =
      C (ι (opU L Q (sgStar L) 0) ^ 2) * (C (px W (ptW l L ι W Q)) - xT W (ptW l L ι W P)) *
        eW l L ι W P ^ 2 := by
  have hT := hS l L ι W hU (piW l L ι W hA hU) (fun _ => rfl)
  unfold IsTransSys at hT
  have key := hT.2.2 P Q hQ
  have hpi : ∀ t, piW l L ι W hA hU t = ptW l L ι W t := fun _ => rfl
  simp only [hpi] at key
  have hPz : ptW l L ι W P ≠ 0 := fun h => hP ((analytic_point_eq_zero_iff l L ι W hU P).1 h)
  have hx2 : x2 W (ptW l L ι W P) = X ^ 2 * xT W (ptW l L ι W P) := by
    rcases h : ptW l L ι W P with _ | ⟨x, y, hxy⟩
    · exact absurd h hPz
    · rfl
  rw [hx2, AnaSysW.cc_gW] at key
  simp only [gW_eq] at key
  have hE : fExp (phW l L ι W) ≠ 0 := by
    intro h0
    have h1 := AnaSysW.fExp_cancel (l := l) (L := L) (ι := ι) (W := W)
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hX : (X : PowerSeries ℂ_[l]) ^ 2 * fExp (phW l L ι W) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hE)
  apply mul_left_cancel₀ hX
  linear_combination key

open Classical in

theorem hW_prod (hS : AnalyticSysW) (hA : PtWAdd) (hU : Unif l L ι W) (t₀ : ℂ) (M : ℕ) (hM : 0 < M)
    (h0 : (M : ℂ) * t₀ ∈ L.lattice) (h0' : t₀ ∉ L.lattice) (a b p q : ℂ)
    (ha : (M : ℂ) * a ∈ L.lattice) (hb : (M : ℂ) * b ∈ L.lattice) (hp : (M : ℂ) * p ∈ L.lattice)
    (hq : (M : ℂ) * q ∈ L.lattice) (hab : a - (p + q) ∈ L.lattice) (hbb : b - (p - q) ∈ L.lattice)
    (hq' : ptW l L ι W q ≠ 0) (hp' : p + t₀ ∉ L.lattice) :
    Sim (hW l L ι W t₀ a * hW l L ι W t₀ b)
      (C (ι (opU L q (sgStar L) 0) ^ 2) * (C (px W (ptW l L ι W q)) - xT W (ptW l L ι W (p + t₀))) *
        hW l L ι W t₀ p ^ 2) := by
  have h1 : Sim (hW l L ι W t₀ a) (C (ι (opU L t₀ (sgStar L) 0))⁻¹ * eW l L ι W (p + t₀ + q)) := by
    refine (hW_sim l L ι W t₀ a M hM ha h0 h0').trans (Sim.mul_left _ ?_)
    refine eW_sim l L ι W _ _ M hM ?_ ?_
    · rw [mul_add, mul_add]
      exact add_mem (add_mem hp h0) hq
    · have e : a + t₀ - (p + t₀ + q) = a - (p + q) := by ring
      rw [e]
      exact hab
  have h2 : Sim (hW l L ι W t₀ b) (C (ι (opU L t₀ (sgStar L) 0))⁻¹ * eW l L ι W (p + t₀ - q)) := by
    refine (hW_sim l L ι W t₀ b M hM hb h0 h0').trans (Sim.mul_left _ ?_)
    refine eW_sim l L ι W _ _ M hM ?_ ?_
    · rw [mul_sub, mul_add]
      exact sub_mem (add_mem hp h0) hq
    · have e : b + t₀ - (p + t₀ - q) = b - (p - q) := by ring
      rw [e]
      exact hbb
  have h3 := hW_sim l L ι W t₀ p M hM hp h0 h0'
  have h4 := h1.mul h2
  have e : C (ι (opU L t₀ (sgStar L) 0))⁻¹ * eW l L ι W (p + t₀ + q) *
      (C (ι (opU L t₀ (sgStar L) 0))⁻¹ * eW l L ι W (p + t₀ - q)) =
      C (ι (opU L q (sgStar L) 0) ^ 2) * (C (px W (ptW l L ι W q)) - xT W (ptW l L ι W (p + t₀))) *
        (C (ι (opU L t₀ (sgStar L) 0))⁻¹ * eW l L ι W (p + t₀)) ^ 2 := by
    rw [mul_mul_mul_comm, eW_prod hS hA hU (p + t₀) q hp' hq']
    ring
  rw [e] at h4
  exact h4.trans (Sim.mul_left _ h3.sq.symm)

end An

end TransW

open TransW

open Classical in

theorem AnalyticTransW_of (hS : AnalyticSysW) (hA : PtWAdd) (hZ : PtWZero) : AnalyticTransW := by
  intro l _ L ι W hU hW t N _ hlN hNt ht
  obtain ⟨hIP, hTS⟩ := restrict hS hA hZ hU hW t N hlN hNt
  have h := transUnit ℂ_[l] W hW (AddSubgroup.zmultiples t) _ _ hIP hTS
    ⟨t, AddSubgroup.mem_zmultiples t⟩ N (Tor.norm_natCast l hlN)
    (by
      change N • ptW l L ι W t = 0
      rw [nsmul_ptW hA hU]
      exact (hZ l L ι W hU _).2 hNt)
    (fun h0 => ht ((hZ l L ι W hU t).1 h0))
  simpa only [AnaSysW.cc_gW] using h

namespace TransW

section Cases

variable {l : ℕ} [Fact l.Prime] {L : PeriodPair} {ι : ℂ ≃+* ℂ_[l]} {W : WeierstrassCurve ℂ_[l]}

theorem half_mem {ω₀ : ℂ} (hω : ω₀ ∈ L.lattice) (N : ℕ) : ((2 * N : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by
  have h : ((2 * N : ℕ) : ℂ) * (ω₀ / 2) = N • ω₀ := by
    rw [nsmul_eq_mul]
    push_cast
    ring
  rw [h]
  exact nsmul_mem hω N

theorem two_mem {t : ℂ} {N : ℕ} (h : (N : ℂ) * t ∈ L.lattice) : ((2 * N : ℕ) : ℂ) * t ∈ L.lattice := by
  have h2 : ((2 * N : ℕ) : ℂ) * t = 2 • ((N : ℂ) * t) := by
    rw [nsmul_eq_mul]
    push_cast
    ring
  rw [h2]
  exact nsmul_mem h 2

open Classical in

theorem oddCase (hS : AnalyticSysW) (hA : PtWAdd) (hZ : PtWZero) (hU : Unif l L ι W) (hW : IntCurve W)
    (hl2 : l ≠ 2) (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice) (hω2 : ω₀ / 2 ∉ L.lattice)
    (hOne : OneUnit (inW l ι W (th0 L (ω₀ / 2)))) (s : ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ l ∣ N)
    (hNs : (N : ℂ) * s ∈ L.lattice) : GaussOne (TransW.hW l L ι W (ω₀ / 2) s) := by
  obtain ⟨-, -, -, -, -, -, oMul, -, oInv, -⟩ := intRules ℂ_[l]
  have hl2' : ¬ l ∣ 2 := fun h => hl2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have h2t : ((2 : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by simpa using half_mem hω 1
  obtain ⟨hc1, hOne'⟩ := AnalyticTransW_of hS hA hZ l L ι W hU hW (ω₀ / 2) 2 (by norm_num) hl2' h2t hω2
  have hth : th0 L (ω₀ / 2) =
      fun z => (opU L (ω₀ / 2) (sgStar L) 0)⁻¹ * opU L (ω₀ / 2) (sgStar L) z := by
    funext z
    rw [th0, div_eq_inv_mul]
  have hin : inW l ι W (th0 L (ω₀ / 2)) =
      C (ι (opU L (ω₀ / 2) (sgStar L) 0))⁻¹ * eW l L ι W (ω₀ / 2) := by
    rw [hth, inW_const_mul, map_inv₀]
    rfl
  have e1 : C (ι (opU L (ω₀ / 2) (sgStar L) 0))⁻¹ * gW l L ι W (ω₀ / 2) =
      fExp (phW l L ι W) * inW l ι W (th0 L (ω₀ / 2)) := by
    rw [hin, gW_eq]
    ring
  rw [e1] at hOne'
  have hcc : constantCoeff (inW l ι W (th0 L (ω₀ / 2))) ≠ 0 := by
    rw [hOne.1]
    exact one_ne_zero
  have hinv : OneUnit (inW l ι W (th0 L (ω₀ / 2)))⁻¹ :=
    oInv _ _ hOne (PowerSeries.mul_inv_cancel _ hcc)
  have hE : OneUnit (fExp (phW l L ι W)) := by
    have := oMul _ _ hOne' hinv
    rwa [mul_assoc, PowerSeries.mul_inv_cancel _ hcc, mul_one] at this
  have hE' : OneUnit (fExp (-(phW l L ι W))) := oInv _ _ hE (AnaSysW.fExp_cancel l L ι W)
  have hN2 : ¬ l ∣ 2 * N := fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim hl2' hlN
  have m3 : ((2 * N : ℕ) : ℂ) * (s + ω₀ / 2) ∈ L.lattice := by
    rw [mul_add]
    exact add_mem (two_mem hNs) (half_mem hω N)
  refine (hW_sim l L ι W (ω₀ / 2) s (2 * N) (by omega) (two_mem hNs) (half_mem hω N) hω2).gaussOne ?_
  refine Tor.gaussOne_C_mul (by rw [norm_inv, hc1, inv_one]) ?_
  rw [eW_eq]
  exact gaussMul ℂ_[l] _ _ (gaussOne_of_oneUnit hE') (gW_gauss hS hA hZ hU hW _ (2 * N) hN2 m3)

open Classical in

theorem shiftCase (hS : AnalyticSysW) (hA : PtWAdd) (hZ : PtWZero) (hU : Unif l L ι W) (hW : IntCurve W)
    (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice) (hω2 : ω₀ / 2 ∉ L.lattice)
    (hx : ‖px W (ptW l L ι W (ω₀ / 2))‖ ≤ 1)
    (hOne : OneUnit (inW l ι W (th0 L (ω₀ / 2)))) (s : ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ l ∣ N)
    (hodd : ¬ 2 ∣ N) (hNs : (N : ℂ) * s ∈ L.lattice) : GaussOne (TransW.hW l L ι W (ω₀ / 2) s) := by
  have hz := hZ l L ι W hU
  have hadd := hA l L ι W hU
  have hNP : N • ptW l L ι W s = 0 := by
    rw [nsmul_ptW hA hU]
    exact (hz _).2 hNs
  have hfin : IsOfFinAddOrder (ptW l L ι W s) := isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, hNP⟩
  have : Finite (AddSubgroup.zmultiples (ptW l L ι W s)) := finite_zmultiples.2 hfin
  have hcard : ‖(Nat.card (AddSubgroup.zmultiples (ptW l L ι W s)) : ℂ_[l])‖ = 1 := by
    rw [Nat.card_zmultiples]
    exact Tor.norm_natCast l (fun h => hlN (h.trans (addOrderOf_dvd_of_nsmul_eq_zero hNP)))
  have hrep : ∀ P ∈ AddSubgroup.zmultiples (ptW l L ι W s),
      ∃ t : ℂ, (N : ℂ) * t ∈ L.lattice ∧ ptW l L ι W t = P := by
    intro P hP
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hP
    refine ⟨(k : ℂ) * s, ?_, (zsmul_ptW hA hU s k).symm⟩
    have e : (N : ℂ) * ((k : ℂ) * s) = (k : ℂ) * ((N : ℂ) * s) := by ring
    rw [e]
    exact Tor.int_mul_mem L k hNs
  have hkill : ∀ P ∈ AddSubgroup.zmultiples (ptW l L ι W s), N • P = 0 := by
    intro P hP
    obtain ⟨t, ht, rfl⟩ := hrep P hP
    rw [nsmul_ptW hA hU]
    exact (hz _).2 ht
  have hSS : ptW l L ι W (ω₀ / 2) + ptW l L ι W (ω₀ / 2) = 0 := by
    rw [← hadd, add_halves]
    exact (hz _).2 hω
  have hS0 : ptW l L ι W (ω₀ / 2) ≠ 0 := fun h => hω2 ((hz _).1 h)
  have hSA : ptW l L ι W (ω₀ / 2) ∉ AddSubgroup.zmultiples (ptW l L ι W s) := by
    intro hmem
    have h1 := hkill _ hmem
    obtain ⟨k, hk⟩ : ∃ k, N = 2 * k + 1 := ⟨N / 2, by omega⟩
    rw [hk, add_nsmul, one_nsmul, mul_nsmul, two_nsmul, hSS, nsmul_zero, zero_add] at h1
    exact hS0 h1
  have hy : ‖py W (ptW l L ι W (ω₀ / 2))‖ ≤ 1 :=
    Shift.py_int W ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩ _ hx
  obtain ⟨hAint, hSint⟩ := shiftPtsInt ℂ_[l] W hW (AddSubgroup.zmultiples (ptW l L ι W s)) hcard
    (ptW l L ι W (ω₀ / 2)) hSA hSS hx hy

  let rep : W.toAffine.Point → ℂ := fun P =>
    if P = 0 then 0 else
      if h : ∃ t : ℂ, (N : ℂ) * t ∈ L.lattice ∧ ptW l L ι W t = P then h.choose else 0
  have rep0 : rep 0 = 0 := if_pos rfl
  have repS : ∀ P ∈ AddSubgroup.zmultiples (ptW l L ι W s),
      (N : ℂ) * rep P ∈ L.lattice ∧ ptW l L ι W (rep P) = P := by
    intro P hP
    by_cases h0 : P = 0
    · subst h0
      rw [rep0, mul_zero]
      exact ⟨zero_mem _, (hz 0).2 (zero_mem _)⟩
    · have h := hrep P hP
      have e : rep P = h.choose := by
        change (if P = 0 then 0 else
          if h : ∃ t : ℂ, (N : ℂ) * t ∈ L.lattice ∧ ptW l L ι W t = P then h.choose else 0) = _
        rw [if_neg h0, dif_pos h]
      rw [e]
      exact h.choose_spec
  have hsys : IsShiftSys W (AddSubgroup.zmultiples (ptW l L ι W s)) (ptW l L ι W (ω₀ / 2))
      (fun P => TransW.hW l L ι W (ω₀ / 2) (rep P)) (fun Q => ι (opU L (rep Q) (sgStar L) 0)) := by
    refine ⟨?_, ?_, ?_⟩
    · change OneUnit (TransW.hW l L ι W (ω₀ / 2) (rep 0))
      rw [rep0]
      have e : opU L 0 (th0 L (ω₀ / 2)) = th0 L (ω₀ / 2) := by
        funext z
        exact (Formalism.L2.Th1.F.opUComm L _ z).1
      rw [TransW.hW, e]
      exact hOne
    · intro Q hQ hQ0
      have h := (hS l L ι W hU (piW l L ι W hA hU) (fun _ => rfl)).2.1 (rep Q)
        (by
          change ptW l L ι W (rep Q) ≠ 0
          rw [(repS Q hQ).2]
          exact hQ0)
      rwa [AnaSysW.cc_gW] at h
    · intro P hP Q hQ hQ0
      have hPQ := add_mem hP hQ
      have hPQ' := sub_mem hP hQ
      have key := hW_prod hS hA hU (ω₀ / 2) (2 * N) (by omega) (half_mem hω N) hω2
        (rep (P + Q)) (rep (P - Q)) (rep P) (rep Q)
        (two_mem (repS _ hPQ).1) (two_mem (repS _ hPQ').1) (two_mem (repS _ hP).1)
        (two_mem (repS _ hQ).1)
        (by
          rw [← hz, sub_ptW hA hU, hadd, (repS _ hPQ).2, (repS _ hP).2, (repS _ hQ).2, sub_self])
        (by
          rw [← hz, sub_ptW hA hU, sub_ptW hA hU, (repS _ hPQ').2, (repS _ hP).2, (repS _ hQ).2,
            sub_self])
        (by
          rw [(repS Q hQ).2]
          exact hQ0)
        (by
          intro hmem
          have h1 := (hz _).2 hmem
          rw [hadd, (repS _ hP).2] at h1
          apply hSA
          rw [← neg_eq_of_add_eq_zero_right h1]
          exact neg_mem hP)
      obtain ⟨ρ, hρ, hk⟩ := key
      refine ⟨ρ, hρ, ?_⟩
      rw [hadd, (repS _ hP).2, (repS _ hQ).2] at hk
      rw [hk, map_mul]
      ring
  obtain ⟨hn, ho⟩ := (shiftUnit ℂ_[l] W hW (AddSubgroup.zmultiples (ptW l L ι W s)) hcard
    (ptW l L ι W (ω₀ / 2)) hSA hAint hSint _ _ hsys).2 (ptW l L ι W s)
    (AddSubgroup.mem_zmultiples _)
  have hs := repS _ (AddSubgroup.mem_zmultiples (ptW l L ι W s))
  refine (hW_sim_hW l L ι W (ω₀ / 2) s (rep (ptW l L ι W s)) (2 * N) (by omega) (two_mem hNs)
    (two_mem hs.1) (half_mem hω N) hω2 ?_).gaussOne (gaussOne_of_shape hn ho)
  rw [← hz, sub_ptW hA hU, hs.2, sub_self]

end Cases

end TransW

theorem ShiftAnalyticW_of (hS : AnalyticSysW) (hA : PtWAdd) (hZ : PtWZero) : ShiftAnalyticW := by
  intro l _ L ι W hU hW ω₀ hω hω2 hx hOne s N hN hlN hNs
  by_cases hl2 : l = 2
  · exact shiftCase hS hA hZ hU hW ω₀ hω hω2 hx hOne s N hN hlN (hl2 ▸ hlN) hNs
  · exact oddCase hS hA hZ hU hW hl2 ω₀ hω hω2 hOne s N hN hlN hNs

theorem analytic_translate_model : AnalyticTransW := AnalyticTransW_of analytic_translate_system_model analytic_point_map_add analytic_point_eq_zero_iff

theorem shift_analytic_model : ShiftAnalyticW := ShiftAnalyticW_of analytic_translate_system_model analytic_point_map_add analytic_point_eq_zero_iff

end Formalism.L2.Th1.E

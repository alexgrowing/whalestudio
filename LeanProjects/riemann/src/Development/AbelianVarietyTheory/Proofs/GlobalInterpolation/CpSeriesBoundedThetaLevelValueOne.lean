import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPoles
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe

noncomputable section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate Topology

namespace GlobalTheory.MomN.ThetaQuot

variable {q : ℕ} [Fact q.Prime]

theorem bdd_hat_quot (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (hC : M.Chart ℓ) (F H : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hH : Differentiable ℂ H) (h0 : H 0 ≠ 0)
    (hper : ∀ l ∈ M.L.lattice, ∀ z, F (z + l) / H (z + l) = F z / H z)
    (hz : ∀ p, H p = 0 → ¬ M.Small p) :
    Bdd (hat M.ι ℓ fun z => F z / H z) := by
  refine EllBdd.bdd_hat_of_ell q M ℓ _ hC ⟨fun z => ?_, hper⟩ ((hF.analyticAt 0).div (hH.analyticAt 0) h0)
    fun p hp => hz p ?_
  · exact (hF.analyticAt z).meromorphicAt.div (hH.analyticAt z).meromorphicAt
  · by_contra hne
    exact absurd hp (not_lt.2 ((hF.analyticAt p).div (hH.analyticAt p) hne).meromorphicOrderAt_nonneg)

theorem not_inOK_half {d : ℕ} (hd : 0 < d) : ¬ InOK d (1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : Real.sqrt d ≠ 0 := by positivity
  have h2 := congrArg Complex.im h
  have h1' := congrArg Complex.re h
  simp [wK, hs] at h1' h2
  subst h2
  have : (1 : ℝ) = 2 * u := by linarith
  have : (1 : ℤ) = 2 * u := by exact_mod_cast this
  omega

theorem bd_one_hat_of_theta_level : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ G : ℂ → ℂ) (a : ℕ), d.Prime → d % 16 = 7 → Split d q → q ≠ 2 → IsOK d M.L → M.MChart ω → IsTh d θ → Differentiable ℂ G → G 0 = 1 → (∀ x, InOK d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x)) ^ a = G z) → (∀ z, G z = 0 → PrimeTo d q z) → Bd 1 (hat M.ι (C ω * logS) G) := by
  intro d q _ M ω θ G a hd hd16 hsp hq2 hOK hMC hθ hG hG0 hGW hGz
  have hθB := theta_series_integral d q M ω θ hd hd16 hsp hOK hMC hθ
  have hC : M.Chart (C ω * logS) := hMC
  set ℓ := C ω * logS with hℓ
  have hOk := hC.1
  have hℓ0 : constantCoeff ℓ = 0 := hC.2.1
  obtain ⟨hθd, hθ0, -, hθW, hθz⟩ := hθ
  set E : ℂ → ℂ → ℂ := fun z x => Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) *
    Complex.exp (-(Real.pi : ℂ) * h1 d z x - (Real.pi : ℂ) / 2 * h1 d x x) with hE
  have hE0 : ∀ z x, E z x ≠ 0 := fun z x => mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have hθE : ∀ x, InOK d x → ∀ z, θ (z + x) * E z x = θ z := by
    intro x hx z
    have := congrFun (hθW x hx) z
    simp only [W1, U1] at this
    rw [← this]; simp only [hE]; ring
  have hGE : ∀ x, InOK d x → ∀ z, G (z + x) * E z x ^ a = G z := hGW
  have hlat : ∀ l, l ∈ M.L.lattice ↔ InOK d l := hOK
  have hper1 : ∀ l ∈ M.L.lattice, ∀ z, G (z + l) / θ (z + l) ^ a = G z / θ z ^ a := by
    intro l hl z
    rw [hlat] at hl
    rw [← hGE l hl z, ← hθE l hl z, mul_pow (θ (z + l)) (E z l) a, mul_div_mul_right _ _ (pow_ne_zero _ (hE0 z l))]
  have hper2 : ∀ l ∈ M.L.lattice, ∀ z, θ (z + l) ^ a / G (z + l) = θ z ^ a / G z := by
    intro l hl z
    rw [hlat] at hl
    rw [← hGE l hl z, ← hθE l hl z, mul_pow (θ (z + l)) (E z l) a, mul_div_mul_right _ _ (pow_ne_zero _ (hE0 z l))]
  have hnsθ : ∀ p, θ p = 0 → ¬ M.Small p := by
    intro p hp
    have hm : p - 1 / 2 ∈ M.L.lattice := (hlat _).2 (hθz p hp)
    have h1m : (1 : ℂ) ∈ M.L.lattice := (hlat _).2 ⟨1, 0, by simp⟩
    have h2 : ((2 : ℕ) : ℂ) * p ∈ M.L.lattice := by
      have : ((2 : ℕ) : ℂ) * p = (p - 1 / 2) + (p - 1 / 2) + 1 := by push_cast; ring
      rw [this]; exact add_mem (add_mem hm hm) h1m
    have hnot : p ∉ M.L.lattice := fun h => not_inOK_half hd.pos ((hlat _).1 (by
      have : (1 / 2 : ℂ) = p - (p - 1 / 2) := by ring
      rw [this]; exact sub_mem h hm))
    have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hq2)
    have hx := (TorsionReduction.torsion_integral_and_distinct q M 2 hOk hcop).1 p h2 hnot
    rintro (h | h)
    · exact hnot h
    · linarith
  have hnsG : ∀ p, G p = 0 → ¬ M.Small p := by
    intro p hp
    obtain ⟨s, -, hsq, hsp'⟩ := hGz p hp
    have hm : (s : ℂ) * p ∈ M.L.lattice := (hlat _).2 hsp'
    have hnot : p ∉ M.L.lattice := fun h => by
      have := hGE p ((hlat _).1 h) 0
      rw [zero_add, hp, zero_mul, hG0] at this
      exact zero_ne_one this
    have hx := (TorsionReduction.torsion_integral_and_distinct q M s hOk hsq).1 p hm hnot
    rintro (h | h)
    · exact hnot h
    · linarith
  have hθa : Differentiable ℂ (fun z => θ z ^ a) := hθd.pow a
  have hθa0 : θ 0 ^ a ≠ 0 := by rw [hθ0, one_pow]; exact one_ne_zero
  have hG0' : G 0 ≠ 0 := by rw [hG0]; exact one_ne_zero
  have hφ := bdd_hat_quot M ℓ hC G (fun z => θ z ^ a) hG hθa hθa0 hper1
    (fun p hp => by
      rcases eq_or_ne a 0 with rfl | ha
      · simp at hp
      · exact hnsθ p ((pow_eq_zero_iff ha).1 hp))
  have hψ := bdd_hat_quot M ℓ hC (fun z => θ z ^ a) G hθa hG hG0' hper2 hnsG
  obtain ⟨hL1, hL2, -, hL4, -, -, -⟩ := TaylorRead.hat_laws q M.ι ℓ hℓ0
  obtain ⟨gl1, -, -, -, gl5, -⟩ := sup_norm_laws q
  have haφ : AnalyticAt ℂ (fun z => G z / θ z ^ a) 0 := (hG.analyticAt 0).div (hθa.analyticAt 0) hθa0
  have haψ : AnalyticAt ℂ (fun z => θ z ^ a / G z) 0 := (hθa.analyticAt 0).div (hG.analyticAt 0) hG0'
  have hθne : ∀ᶠ z in 𝓝 0, θ z ≠ 0 := hθd.continuous.continuousAt.eventually_ne (by rw [hθ0]; exact one_ne_zero)
  have hGne : ∀ᶠ z in 𝓝 0, G z ≠ 0 := hG.continuous.continuousAt.eventually_ne hG0'
  have hprod : hat M.ι ℓ (fun z => G z / θ z ^ a) * hat M.ι ℓ (fun z => θ z ^ a / G z) = 1 := by
    have e1 := (hL1 (fun z => G z / θ z ^ a * (θ z ^ a / G z)) (fun _ => 1) (haφ.mul haψ) analyticAt_const).2.2.1
      (eventually_nhdsWithin_of_eventually_nhds (by
        filter_upwards [hθne, hGne] with z h1 h2
        rw [div_mul_div_comm, mul_comm (G z), div_self (mul_ne_zero (pow_ne_zero _ h1) h2)]))
    rw [← (hL1 _ _ haφ haψ).2.1, e1, hL2]; simp
  have hcc : constantCoeff (hat M.ι ℓ (fun z => G z / θ z ^ a)) = 1 := by
    rw [hL4]; simp [hG0, hθ0]
  have hφ1 : Bd 1 (hat M.ι ℓ (fun z => G z / θ z ^ a)) := (gl5 _ _ hφ hψ hprod hcc).1
  have eG : hat M.ι ℓ G = hat M.ι ℓ (fun z => G z / θ z ^ a) * hat M.ι ℓ (fun z => θ z ^ a) := by
    rw [← (hL1 _ _ haφ (hθa.analyticAt 0)).2.1]
    exact (hL1 G _ (hG.analyticAt 0) (haφ.mul (hθa.analyticAt 0))).2.2.1
      (eventually_nhdsWithin_of_eventually_nhds (by
        filter_upwards [hθne] with z h1
        exact (div_mul_cancel₀ _ (pow_ne_zero _ h1)).symm))
  have hpow : ∀ n : ℕ, hat M.ι ℓ (fun z => θ z ^ n) = hat M.ι ℓ θ ^ n ∧ Bd 1 (hat M.ι ℓ θ ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simpa using hL2 1, fun k => ?_⟩
      rw [pow_zero, coeff_one]; split_ifs <;> simp
    | succ n ih =>
      have e : (fun z => θ z ^ (n + 1)) = fun z => θ z ^ n * θ z := funext fun z => pow_succ _ _
      rw [e, (hL1 (fun z => θ z ^ n) θ ((hθd.pow n).analyticAt 0) (hθd.analyticAt 0)).2.1, ih.1, pow_succ]
      refine ⟨rfl, ?_⟩
      simpa using (gl1 _ _ 1 1 ih.2 hθB).2
  rw [eG, (hpow a).1]
  simpa using (gl1 _ _ 1 1 hφ1 (hpow a).2).2

end GlobalTheory.MomN.ThetaQuot

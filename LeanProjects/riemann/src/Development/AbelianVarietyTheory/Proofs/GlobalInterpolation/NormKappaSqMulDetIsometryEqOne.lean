import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelativeDeterminantIsometryNormOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticAtMostTwoPrimesOverStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugateEmbeddingsInduceDifferentPrimesSplitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationOfGeneratorOfPowStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexPadicNormKappaSplitPrimeStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.KapVal

open IsDedekindDomain

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [NumberField K] (j : K →+* ℂ_[q])
    (y : 𝓞 K) : ‖j (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by
    convert map_isIntegral_int j (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

theorem norm_natCast_lt_one (q : ℕ) [Fact q.Prime] : ‖((q : ℕ) : ℂ_[q])‖ < 1 := by
  have e : ((q : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by
    simp
  rw [e, PadicComplex.norm_extends']
  exact Padic.norm_p_lt_one

end GlobalTheory.KapVal

namespace GlobalTheory.KapVal

open IsDedekindDomain

variable {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [NumberField K]

theorem exists_place (j : K →+* ℂ_[q]) :
    ∃ w : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ w.asIdeal ∧ ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1 := by
  let P : Ideal (𝓞 K) :=
    { carrier := {x | ‖j (x : K)‖ < 1}
      add_mem' := fun {x y} hx hy => by
        show ‖j ((x : K) + (y : K))‖ < 1
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      zero_mem' := by
        show ‖j (0 : K)‖ < 1
        simp
      smul_mem' := fun r x hx => by
        show ‖j ((r : K) * (x : K))‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one_of_int j r) (norm_nonneg _) hx }
  have hP : ∀ x : 𝓞 K, x ∈ P ↔ ‖j (x : K)‖ < 1 := fun _ => Iff.rfl
  have hl : ((q : ℕ) : 𝓞 K) ∈ P := by
    rw [hP]
    have e : j (((q : ℕ) : 𝓞 K) : K) = ((q : ℕ) : ℂ_[q]) := by simp
    rw [e]
    exact norm_natCast_lt_one q
  have hprime : P.IsPrime := by
    refine ⟨?_, fun {x y} hxy => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]
      simp
    · rw [hP] at hxy
      have e : j ((x * y : 𝓞 K) : K) = j (x : K) * j (y : K) := by simp
      rw [e, norm_mul] at hxy
      rw [hP, hP]
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hxy)
  refine ⟨⟨P, hprime, ?_⟩, hl, hP⟩
  intro h0
  rw [h0, Ideal.mem_bot] at hl
  exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast hl)

theorem norm_le_one_of_val (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (x : K) (hx : w.valuation K x ≤ 1) :
    ‖j x‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hd : 1 ≤ ‖j ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have h2 : ‖j x‖ * ‖j ((d : 𝓞 K) : K)‖ = ‖j (n : K)‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun z => ‖j z‖) h
  have h3 := norm_le_one_of_int j n
  nlinarith [norm_nonneg (j x)]

theorem norm_eq_one_of_val (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (x : K) (hx : w.valuation K x = 1) :
    ‖j x‖ = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 := norm_le_one_of_val j w hw x hx.le
  have h2 := norm_le_one_of_val j w hw x⁻¹ (by rw [map_inv₀, hx, inv_one])
  have h3 : ‖j x‖ * ‖j x⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
  nlinarith [norm_nonneg (j x), norm_nonneg (j x⁻¹)]

theorem norm_pow_eq (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (n : ℕ) (π : 𝓞 K)
    (hπ : w.valuation K (π : K) = WithZero.exp (-(n : ℤ))) (x : K) (hx : x ≠ 0) :
    ‖j x‖ ^ n = ‖j (π : K)‖ ^ (-WithZero.log (w.valuation K x)) := by
  set y := -WithZero.log (w.valuation K x) with hy
  have hv0 : w.valuation K x ≠ 0 := by simpa using hx
  have hvx : w.valuation K x = WithZero.exp (-y) := by
    rw [hy, neg_neg, WithZero.exp_log hv0]
  have hπ0 : (π : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hz : w.valuation K (x ^ n * (π : K) ^ (-y)) = 1 := by
    rw [map_mul, map_pow, map_zpow₀, hvx, hπ, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  have h1 := norm_eq_one_of_val j w hw _ hz
  rw [map_mul, map_pow, map_zpow₀, norm_mul, norm_pow, norm_zpow] at h1
  have hjπ : ‖j (π : K)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero j).2 hπ0
  have h2 : ‖j (π : K)‖ ^ (-y) * ‖j (π : K)‖ ^ y = 1 := by
    rw [← zpow_add₀ hjπ, neg_add_cancel, zpow_zero]
  calc ‖j x‖ ^ n = ‖j x‖ ^ n * (‖j (π : K)‖ ^ (-y) * ‖j (π : K)‖ ^ y) := by rw [h2, mul_one]
    _ = (‖j x‖ ^ n * ‖j (π : K)‖ ^ (-y)) * ‖j (π : K)‖ ^ y := by ring
    _ = ‖j (π : K)‖ ^ y := by rw [h1, one_mul]

end GlobalTheory.KapVal

namespace GlobalTheory.KapVal

open IsDedekindDomain

theorem norm_kappa_sq_mul_det : ∀ (D : D7) (γ₀ γ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], q ≠ 2 →
    jacobiSym (-(D.host.d : ℤ)) q = 1 → γ.AtP q → ∀ ι : ℂ ≃+* ℂ_[q],
    ‖ι k.kappa‖ ^ 2 * ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = 1 := by
  intro D γ₀ γ k q _ hq2 hj hat ι
  have hqp : q.Prime := Fact.out
  have hs : SplitK D q := Or.inr hj
  let jK : D.host.K →+* ℂ_[q] := ι.toRingHom.comp (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
  let jK' : D.host.K →+* ℂ_[q] := ι.toRingHom.comp (D.host.φ₀.comp
    ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E)))
  have ejK : ∀ z : D.host.K, jK z = ι (D.host.φ₀ (z : D.host.E)) := fun z => rfl
  have ejK' : ∀ z : D.host.K, jK' z = ι (D.host.φ₀ (D.host.conj (z : D.host.E))) := fun z => rfl
  have hU := GlobalTheory.T.relativeDeterminant_isometry_norm_one D γ₀ γ
  set x : D.host.K := γ.detRel γ₀ with hxdef
  set h : ℕ := classNumber D.host.K with hh
  have hy : ordK (k.pp q) x = k.yP q :=
    yIndep D γ₀ q (k.pp q) γ (k.gaP q) hqp hs (k.pp_over q hqp hs) hat (k.gaP_at q hqp hs)
  have hπv : (k.pp q).valuation D.host.K ((k.pi q : 𝓞 D.host.K) : D.host.K) = WithZero.exp (-(h : ℤ)) :=
    GlobalTheory.T.valuation_eq_exp_neg_of_pow_eq_span_singleton D.host.K (k.pp q) h (k.pi q) (k.pi_gen q hqp hs)
  have hkap := GlobalTheory.T.complexPadic_norm_kappa_splitPrime D γ₀ k q hs ι
  have hrt := k.rt_pow q hqp hs
  have hrt0 := k.rt_ne_zero q hqp hs
  set y : ℤ := k.yP q with hydef
  set 𝔭 := k.pp q with h𝔭
  set π : 𝓞 D.host.K := k.pi q with hπdef
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hU
    simp at hU
  have hxx : ‖jK x‖ * ‖jK' x‖ = 1 := by
    rw [← norm_mul, ejK, ejK', ← map_mul, ← map_mul, hU, map_one, map_one, norm_one]
  obtain ⟨w, hqw, hw⟩ := exists_place jK
  obtain ⟨w', hqw', hw'⟩ := exists_place jK'
  have hne : w ≠ w' := by
    intro heq
    obtain ⟨y0, h1, h2⟩ := GlobalTheory.T.conjugate_embeddings_induce_different_primes_split D q hq2 hj ι
    have a1 : y0 ∈ w.asIdeal := (hw y0).2 (by rw [ejK]; exact h1)
    rw [heq, hw', ejK'] at a1
    exact absurd a1 (not_lt.2 h2)
  have hq𝔭 : ((q : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal := k.pp_over q hqp hs
  have hnot : ∀ v : HeightOneSpectrum (𝓞 D.host.K), v ≠ 𝔭 → π ∉ v.asIdeal := by
    intro v hv hπ
    apply hv
    have h1 : 𝔭.asIdeal ^ h ≤ v.asIdeal := by
      rw [hh, k.pi_gen q hqp hs, Ideal.span_singleton_le_iff_mem]
      exact hπ
    have h2 : 𝔭.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le h1
    have h3 : 𝔭.asIdeal = v.asIdeal := 𝔭.isMaximal.eq_of_le v.isPrime.ne_top h2
    exact (HeightOneSpectrum.ext h3).symm
  have hone : ∀ (j : D.host.K →+* ℂ_[q]) (v : HeightOneSpectrum (𝓞 D.host.K)),
      (∀ z : 𝓞 D.host.K, z ∈ v.asIdeal ↔ ‖j (z : D.host.K)‖ < 1) → v ≠ 𝔭 → ‖j (π : D.host.K)‖ = 1 := by
    intro j v hv hv𝔭
    exact le_antisymm (norm_le_one_of_int j π) (not_lt.1 fun hlt => hnot v hv𝔭 ((hv π).2 hlt))
  have key : ‖jK x‖ ^ h = (‖jK (π : D.host.K)‖ / ‖jK' (π : D.host.K)‖) ^ y := by
    rcases GlobalTheory.T.quadratic_field_at_most_two_primes_over_prime D.host.K (kQuad D) q hqp 𝔭 w w' hq𝔭 hqw hqw' with e | e | e
    · have h1 := norm_pow_eq jK w hw h π (by rw [← e]; exact hπv) x hx0
      have h2 : -WithZero.log (w.valuation D.host.K x) = y := by rw [← e]; exact hy
      rw [h2] at h1
      rw [h1, hone jK' w' hw' (fun e' => hne (e.symm.trans e'.symm)), div_one]
    · have h1 := norm_pow_eq jK' w' hw' h π (by rw [← e]; exact hπv) x hx0
      have h2 : -WithZero.log (w'.valuation D.host.K x) = y := by rw [← e]; exact hy
      rw [h2] at h1
      rw [hone jK w hw (fun e' => hne (e'.trans e)), one_div, inv_zpow', zpow_neg, ← h1]
      have hx' : ‖jK x‖ = ‖jK' x‖⁻¹ := eq_inv_of_mul_eq_one_left hxx
      rw [hx', inv_pow]
    · exact absurd e hne
  have hjx : ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = ‖jK x‖ := rfl
  rw [hjx, hkap]
  rw [← hh] at hrt
  have hr0 : 0 < ‖ι (k.rt q)‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hrt0)
  have hratio : ‖jK (π : D.host.K)‖ / ‖jK' (π : D.host.K)‖ = ‖ι (k.rt q)‖ ^ (2 * h) := by
    rw [ejK, ejK', ← norm_div, ← map_div₀, ← hrt, map_pow, norm_pow]
  rw [hratio] at key
  have hh0 : h ≠ 0 := by rw [hh]; exact (NumberField.classNumber_pos D.host.K).ne'
  have hxr : ‖jK x‖ = ‖ι (k.rt q)‖ ^ (2 * y) := by
    have e : (‖ι (k.rt q)‖ ^ (2 * h)) ^ y = (‖ι (k.rt q)‖ ^ (2 * y)) ^ h := by
      rw [← zpow_natCast, ← zpow_natCast (‖ι (k.rt q)‖ ^ (2 * y)), ← zpow_mul, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e] at key
    exact (pow_left_inj₀ (norm_nonneg _) (zpow_nonneg hr0.le _) hh0).1 key
  rw [hxr, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hr0.ne']
  rw [show -y * ((2 : ℕ) : ℤ) + 2 * y = 0 by push_cast; ring, zpow_zero]

end GlobalTheory.KapVal

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommonRepresentativesPeriodLatticeHalves
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HalfTmul

theorem exists_prime_to_dvd_away {R : Type} [CommRing R] [IsDedekindDomain R] (SS : Finset (HeightOneSpectrum R))
    (m : R) (hm : m ≠ 0) : ∃ t : R, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧
      ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t = m * w := by
  classical
  have hI : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hm
  have hfac : ∀ Q : HeightOneSpectrum R, ∃ n : ℕ, ∃ J : Ideal R, ¬ Q.asIdeal ∣ J ∧ Ideal.span {m} = Q.asIdeal ^ n * J :=
    fun Q => WfDvdMonoid.max_power_factor hI Q.prime.irreducible
  choose n J hJ using hfac
  have hT := Ideal.finite_factors hI
  obtain ⟨t0, ht0⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := SS ∪ hT.toFinset) (fun Q => Q.asIdeal)
    (fun Q => if Q ∈ SS then 1 else n Q) (fun Q _ => Q.prime) (fun Q _ Q' _ h e => h (HeightOneSpectrum.ext e))
    (fun Q => if (Q : HeightOneSpectrum R) ∈ SS then 1 else 0)
  have hone : ∀ Q : HeightOneSpectrum R, (1 : R) ∉ Q.asIdeal := fun Q h1 =>
    Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hSS : ∀ Q ∈ SS, t0 ∉ Q.asIdeal := by
    intro Q hQ hmem
    have h := ht0 Q (Finset.mem_union_left _ hQ)
    simp only [if_pos hQ, pow_one] at h
    exact hone Q (by simpa using Q.asIdeal.sub_mem hmem h)
  have hgood : ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t0 = m * w := by
    intro Q hQ
    by_cases hQT : Q.asIdeal ∣ Ideal.span {m}
    · have h := ht0 Q (Finset.mem_union_right _ (hT.mem_toFinset.2 hQT))
      simp only [if_neg hQ, sub_zero] at h
      obtain ⟨hnd, hEq⟩ := hJ Q
      rw [Ideal.dvd_iff_le] at hnd
      obtain ⟨u, huJ, huQ⟩ := SetLike.not_le_iff_exists.1 hnd
      refine ⟨u, huQ, ?_⟩
      have hmem : t0 * u ∈ Ideal.span {m} := by
        rw [hEq]; exact Ideal.mul_mem_mul h huJ
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 hmem
      exact ⟨w, by rw [mul_comm u, hw]⟩
    · refine ⟨m, ?_, t0, rfl⟩
      intro hmem
      exact hQT (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem))
  by_cases h0 : t0 = 0
  · refine ⟨m, hm, ?_, fun Q _ => ⟨1, hone Q, 1, by ring⟩⟩
    intro Q hQ
    exact absurd (h0 ▸ Q.asIdeal.zero_mem) (hSS Q hQ)
  · exact ⟨t0, h0, hSS, hgood⟩

theorem tmul_mem_of {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (c : ℕ) (hc : 0 < c) (y : W) (hy : y ∈ twist₂ M c (expS SS)) (t : 𝓞 E)
    (ht : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ SS → ∃ u : 𝓞 E, u ∉ Q.asIdeal ∧ ∃ w : 𝓞 E, u * t = (c : 𝓞 E) ^ 2 * w) :
    ((t : E) * (c : E)⁻¹) • y ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcast : ∀ (r : 𝓞 E) (z : W), (r : E) • z = r • z := fun r z => IsScalarTower.algebraMap_smul E r z
  have hcy : (c : E) • y ∈ M := by
    have h := (GlobalTheory.CommonReps.mem_twO_zero M c _).1 (GlobalTheory.CommonReps.natsmul_mem_twO M c _ _ (fun Q => by
      rcases expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num) hy)
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h
  apply Formalism.L2.Ker.mem_of_forall_locP M
  intro Q
  by_cases hQ : Q ∈ SS
  · have h1 := (Formalism.L2.Ker.mem_twO M c _ y).1 hy Q
    simp only [expS, if_pos hQ, zpow_one] at h1
    obtain ⟨s, hs, hsy⟩ := h1
    refine ⟨s, hs, ?_⟩
    have e : s • (((t : E) * (c : E)⁻¹) • y) = t • (s • ((c : E)⁻¹ • y)) := by
      rw [← hcast s, ← hcast t, ← hcast s]
      simp only [smul_smul]
      congr 1; ring
    rw [e]; exact M.smul_mem t hsy
  · obtain ⟨u, hu, w, huw⟩ := ht Q hQ
    refine ⟨u, hu, ?_⟩
    have huwE : (u : E) * (t : E) = (c : E) ^ 2 * (w : E) := by
      have := congrArg (fun r : 𝓞 E => (r : E)) huw
      simpa using this
    have e : u • (((t : E) * (c : E)⁻¹) • y) = w • ((c : E) • y) := by
      rw [← hcast u, ← hcast w]
      simp only [smul_smul]
      congr 1
      field_simp
      linear_combination huwE
    rw [e]; exact M.smul_mem w hcy

theorem exists_tmul_mem_perO : ∀ (D : D7) (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), 0 < c → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ t : 𝓞 D.host.E, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧ ((t : D.host.E) * (c : D.host.E)⁻¹) • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
  intro D a b N N' SS c hc y hy
  obtain ⟨t, ht0, hSS, hgood⟩ := exists_prime_to_dvd_away SS ((c : 𝓞 D.host.E) ^ 2)
    (pow_ne_zero _ (by exact_mod_cast hc.ne'))
  exact ⟨t, ht0, hSS, tmul_mem_of _ SS c hc y hy t hgood⟩

end GlobalTheory.HalfTmul

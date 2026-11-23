import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem cast_dvd {a b : ℕ} : (a : 𝓞 ℚ) ∣ (b : 𝓞 ℚ) ↔ a ∣ b := by
  refine ⟨fun h => ?_, fun h => Nat.cast_dvd_cast h⟩
  have h1 := map_dvd Rat.ringOfIntegersEquiv h
  rw [map_natCast, map_natCast] at h1
  exact Int.natCast_dvd_natCast.1 h1

private theorem mem_iff_dvd (N : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (N : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ N := by
  rw [← cast_dvd, ← Ideal.mem_span_singleton, ← (UpperTheory.V.Af.Nf.places v).2.1]

theorem UpperTheory.heightOneSpectrum_rat_correspond_primes :
    (∀ v : H.P ℚ, (normV v).Prime) ∧ (∀ p : ℕ, p.Prime → ∃ v : H.P ℚ, normV v = p) ∧ (∀ v v' : H.P ℚ, normV v = normV v' → v = v') ∧
          (∀ (N : ℕ) (v : H.P ℚ), Bad N v ↔ normV v ∣ N) := by
  refine ⟨fun v => (UpperTheory.V.Af.Nf.places v).1, fun p hp => ?_, fun v v' h => ?_, fun N v => mem_iff_dvd N v⟩
  · have hnt : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_dvd_one, ← Nat.cast_one, cast_dvd, Nat.dvd_one]
      exact hp.ne_one
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hnt
    have hpM : (p : 𝓞 ℚ) ∈ M := hle (Ideal.mem_span_singleton_self _)
    have hM0 : M ≠ ⊥ := by
      rintro rfl
      exact hp.ne_zero (Nat.cast_eq_zero.1 (Ideal.mem_bot.1 hpM))
    let w : HeightOneSpectrum (𝓞 ℚ) := ⟨M, hM.isPrime, hM0⟩
    exact ⟨w, (Nat.prime_dvd_prime_iff_eq (UpperTheory.V.Af.Nf.places w).1 hp).1 ((mem_iff_dvd p w).1 hpM)⟩
  · apply HeightOneSpectrum.ext
    rw [(UpperTheory.V.Af.Nf.places v).2.1, (UpperTheory.V.Af.Nf.places v').2.1, h]

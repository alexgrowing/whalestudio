import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIsTheRun
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unitary_string_forces_long_part : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c : ℕ) (d : Fin c → ℕ)
    (S : Fin c → Multiset ℂˣ) (T : Multiset ℂˣ) (t : ℕ) (ν : ℂ),
  1 ≤ t → (∀ i, ∀ s ∈ S i, ‖(s : ℂ)‖ = 1) → ‖ν‖ = 1 →
  ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
    T.map (fun z => (z : ℂ)) →
  (Multiset.range t).map (fun c : ℕ => ν * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤
    T.map (fun z => (z : ℂ)) →
  ∃ i, t ≤ d i := by
  intro E _ _ w c d S T t ν ht hS hν hsum hle
  have hN1 : 1 < Ideal.absNorm w.asIdeal := by
    have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
    omega
  set N := Ideal.absNorm w.asIdeal with hN
  have hmem : ν * ((N : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ T.map (fun z => (z : ℂ)) :=
    Multiset.mem_of_le hle (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), rfl⟩)
  rw [← hsum] at hmem
  obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hmem
  obtain ⟨k, -, hk⟩ := Multiset.mem_sum.1 hi
  obtain ⟨s, hs, hsk⟩ := Multiset.mem_map.1 hk
  have hs1 : ‖s‖ = 1 := by
    simp only [Multiset.bind_def, Multiset.pure_def, Multiset.mem_bind, Multiset.mem_singleton] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    exact hS i u hu
  have hNpos : 0 < N := by omega
  have hn := congrArg (fun z : ℂ => ‖z‖) hsk
  simp only [norm_mul, hs1, hν, one_mul, Complex.norm_natCast_cpow_of_pos hNpos] at hn
  have hre : ((((d i : ℂ) - 1) / 2 - ((k : ℕ) : ℂ))).re = ((d i : ℝ) - 1) / 2 - (k : ℕ) := by simp
  have hre2 : ((((t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))).re = ((t : ℝ) - 1) / 2 := by simp
  rw [hre, hre2] at hn
  have hN1' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hle' := (Real.rpow_le_rpow_left_iff hN1').1 hn.ge
  have hk' : ((k : ℕ) : ℝ) ≥ 0 := by positivity
  refine ⟨i, ?_⟩
  have : (t : ℝ) ≤ d i := by linarith
  exact_mod_cast this

end GlobalTheory

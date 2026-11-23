import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalRingCardinality.HostCls
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

private theorem hH_hP (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    ∃ h : Nat.Coprime p 2, D.R.hH (D.R.iota (hP D p)) =
      hcl D.R.e (ZMod.unitOfCoprime p (Nat.Coprime.pow_right (D.R.e + 2) h)) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : D.host.cls 2 = PrimeClass.ram2 := Formalism.BasicNotions.primeClass_two D.host.toHostRaw
    have hc' : D.host.cls 2 = PrimeClass.inertClass := hc
    rw [h2] at hc'
    cases hc'
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  refine ⟨hcop, ?_⟩
  have hN : ¬ p ∣ D.host.condN := Formalism.BasicNotions.not_dvd_conductor_of_inert hp (show D.host.cls p = PrimeClass.inertClass from hc)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨P, hPm, hPl⟩ : ∃ P : Ideal (𝓞 D.host.E), P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
    first
    | exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral _
    | exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral _ _
    | exact Ideal.exists_ideal_liesOver_maximal_of_isIntegral _
    | (obtain ⟨Q, hQm, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E)
          (Ideal.span {(p : ℤ)}) (by simp)
       exact ⟨Q, hQm, ⟨hQc.symm⟩⟩)
  haveI : P.IsPrime := hPm.isPrime
  obtain ⟨⟨σ, hσ⟩, -, -, -⟩ := D.host.der.frob p hN P
  have hmem : D.host.galE σ ∈ frobSet D p := ⟨P, inferInstance, hPl, σ, hσ, rfl⟩
  obtain ⟨P', hP'p, hP'l, σ', hσ', hgal⟩ := Classical.epsilon_spec ⟨_, hmem⟩
  obtain ⟨-, -, h3, -⟩ := D.host.der.frob p hN P'
  obtain ⟨-, -, v, hv, hvh⟩ := h3 σ' hσ'
  unfold hP
  simp only [Formalism.HC.Frame.iota_iotaInv]
  rw [← hgal, show ZMod.unitOfCoprime p (Nat.Coprime.pow_right (D.R.e + 2) hcop) = v from
    Units.ext (by rw [ZMod.coe_unitOfCoprime, hv])]
  exact hvh

theorem two_readings_of_Frobenius (D : D7) : Formalism.MainNotions.CornerGLContinuity.FrobeniusClassCompatibility D := by
  intro p hp hc
  obtain ⟨h2, hh⟩ := hH_hP D p hp hc
  refine ⟨fun h => ?_, ?_⟩
  · subst h
    exact absurd h2 (by decide)
  unfold Formalism.MainNotions.GlobalTheoryTheory.hOf
  split_ifs with hcond
  rw [Formalism.BasicNotions.iotaH_iotaHInv, ← hh]
  rfl

end Formalism.MainNotions.J

end

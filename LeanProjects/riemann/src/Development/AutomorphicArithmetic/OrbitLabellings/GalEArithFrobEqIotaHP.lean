import Mathlib
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.LocalRingCardinality.HostCls

open scoped BigOperators
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical

theorem UpperTheory.galE_arithFrob_eq_iota_hP :
    ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p →
    ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    D.host.galE σ = (Formalism.FrobeniusOrbits.c0, D.R.iota (hP D p)) ∧ orderOf (D.host.galE σ).2 = addOrderOf (hP D p) := by
  intro D p hp hc P hP1 hP2 σ hσ
  have hcl : primeClass D.host.toHostRaw p = PrimeClass.inertClass := hc
  obtain ⟨hN, hj, hps⟩ := (primeClass_eq_inert_iff_symbols hp).1 hcl
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p D.host.condN := hp.coprime_iff_not_dvd.2 hN
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hP1, hP2, σ, hσ, rfl⟩
  obtain ⟨P', hP'1, hP'2, σ', hσ', hg⟩ := Classical.epsilon_spec hne
  have e1 := (D.host.frob_iff p hcop P σ).1 hσ
  have e2 := (D.host.frob_iff p hcop P' σ').1 hσ'
  have h1 : (D.host.galE σ).1 = Formalism.FrobeniusOrbits.c0 := (D.host.hostClasses p hN P σ hσ).2.2.2 ⟨hj, hps⟩
  have h2 : (D.host.galE σ).2 = D.R.iota (hP D p) := by
    unfold hP
    rw [Formalism.HC.Frame.iota_iotaInv, ← hg, e1, e2]
  exact ⟨Prod.ext h1 h2, by rw [h2, Formalism.HC.Frame.orderOf_iota]⟩

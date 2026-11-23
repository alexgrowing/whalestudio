import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowerEmbedding
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobSign

theorem frobG_isArithFrob_and_sign : ∀ (D : D7) (l : ℕ) [Fact l.Prime], l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d →
    (∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q) ∧
    ((((DV.frobG D l).1.2 : ℤˣ) : ℤ) = jacobiSym (-(D.host.d : ℤ)) l) := by
  intro D l hl h2 hq hd
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  have hall : ∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q :=
    fun Q _ _ => GlobalTheory.FrobEmb.isArithFrobAt_frobG D l hl.out Q
  refine ⟨hall, ?_⟩
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have hlI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hlZ.ne_zero).2 hlZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  have hg : D.host.gal (D.host.sigmaOf (DV.frobG D l)) = DV.frobG D l := MulEquiv.apply_symm_apply _ _
  have h := ((D.host.der.frob l hlN P).2.2.1 _ (hall P)).2.1
  rw [hg] at h
  exact h

end GlobalTheory.FrobSign

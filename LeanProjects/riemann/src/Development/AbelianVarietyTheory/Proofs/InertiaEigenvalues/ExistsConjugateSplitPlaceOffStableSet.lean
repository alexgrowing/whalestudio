import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorBaseChangeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlaceOff

open Formalism.HermitianLattices.Ext.L3

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isConjPl_iff (D : D7) (P Q : PlE D.host) :
    IsConjPl D.host P Q ↔ ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ conjO D.host.E x ∈ Q.asIdeal := by
  constructor
  · intro h x
    exact h x (conjO D.host.E x) (by rw [conjO_coe, star_eq_hostConj])
  · intro h x y hy
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    subst this
    exact h x

noncomputable def conjPl (D : D7) (P : PlE D.host) : PlE D.host where
  asIdeal := P.asIdeal.comap (conjO D.host.E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : conjO D.host.E x ∈ P.asIdeal.comap (conjO D.host.E) := by
      rw [Ideal.mem_comap, conjO_conjO]; exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← conjO_conjO (K := D.host.E) x, this, map_zero]

theorem mem_conjPl (D : D7) (P : PlE D.host) (x : 𝓞 D.host.E) :
    x ∈ (conjPl D P).asIdeal ↔ conjO D.host.E x ∈ P.asIdeal := Iff.rfl

theorem conjPl_conjPl (D : D7) (P : PlE D.host) : conjPl D (conjPl D P) = P := by
  ext x
  rw [mem_conjPl, mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl (D : D7) (P : PlE D.host) : IsConjPl D.host P (conjPl D P) := by
  rw [isConjPl_iff]
  intro x
  rw [mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl' (D : D7) (P : PlE D.host) : IsConjPl D.host (conjPl D P) P := by
  rw [isConjPl_iff]
  intro x
  rfl

theorem conjIdeal_eq (D : D7) (P : PlE D.host) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (conjPl D P).asIdeal :=
  conjIdeal_eq_comap _

theorem isSplitPl_iff (D : D7) (P : PlE D.host) :
    IsSplitPl D.host P ↔ ∃ x : 𝓞 D.host.E, x ∈ P.asIdeal ∧ conjO D.host.E x ∉ P.asIdeal := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, h _ (by rw [conjO_coe, star_eq_hostConj])⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun y hy => ?_⟩
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    rw [this]; exact h

theorem conjPl_ne_of_split (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    (conjPl D P).asIdeal ≠ P.asIdeal := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  intro he
  apply hcx
  rw [← mem_conjPl, he]
  exact hx

theorem isSplitPl_conjPl (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    IsSplitPl D.host (conjPl D P) := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  rw [isSplitPl_iff]
  refine ⟨conjO D.host.E x, ?_, ?_⟩
  · rw [mem_conjPl, conjO_conjO]; exact hx
  · rw [mem_conjPl, conjO_conjO]; exact hcx

theorem exists_conj_off (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E))
    (P : PlE D.host)
    (hS0 : ∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0)
    (h2 : placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)))
    (hb : ∀ Q ∈ Sb, Q ∈ S0) (hP : IsSplitPl D.host P) (hPS : P ∉ S0) :
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  have hP'S : conjPl D P ∉ S0 := fun h => hPS (hS0 _ _ h (isConjPl_conjPl' D P))
  have hne := conjPl_ne_of_split D hP
  refine ⟨conjPl D P, isConjPl_conjPl D P, isSplitPl_conjPl D hP, hP'S, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [conjIdeal_eq]; exact hne, fun h => hPS (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq] at he
    have : Q = conjPl D P := HeightOneSpectrum.ext he
    exact hP'S (this ▸ hb Q (by exact_mod_cast hQ))
  · refine ⟨by rw [conjIdeal_eq, conjPl_conjPl]; exact hne.symm,
      fun h => hP'S (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq, conjPl_conjPl] at he
    have : Q = P := HeightOneSpectrum.ext he
    exact hPS (this ▸ hb Q (by exact_mod_cast hQ))
  · exact fun h => hPS (h2 h)
  · exact fun h => hP'S (h2 h)

end GlobalTheory.ConjPlaceOff

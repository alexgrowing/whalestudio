import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ShapeDegreeParity
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TeichmullerFactorisation

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.InertCompare

section Emb

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

theorem embT_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom

def rhoH (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

theorem rhoH_apply (τ : D.what₂.Tau) (x : D.host.E) : rhoH D lam τ x = lamC lam (embT D τ x) := by
  unfold lamC
  rw [dif_pos (embT_mem D τ x)]
  rfl

theorem coe_rhoH (τ : D.what₂.Tau) : (rhoH D lam τ : D.host.E → ℂ_[l]) = tauEmb D lam τ :=
  funext fun x => rhoH_apply D lam τ x

def rhoC (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] := (rhoH D lam τ).comp (D.host.conj : D.host.E →+* D.host.E)

theorem rhoC_apply (τ : D.what₂.Tau) (x : D.host.E) :
    rhoC D lam τ x = lamC lam (embT D τ (D.host.conj x)) := rhoH_apply D lam τ _

def parProj (r : Bool × HH D) (ε : ℕ) (y : D.what₂.Tau → ℂ_[l] × ℂ_[l]) : ZMod (nP D l) → ℂ_[l] :=
  fun s => if s.val % 2 = ε then (y (tauPl D (posPl D l r s.val))).1 else 0

end Emb

def SamePrime {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ ρ' : E →+* ℂ_[l]) : Prop :=
  ∀ a : 𝓞 E, ‖ρ (a : E)‖ < 1 ↔ ‖ρ' (a : E)‖ < 1

theorem tauPl_bijective (D : D7) : Function.Bijective (tauPl D) := by
  have hinj := D.R.toFrame.iota_bijective.1
  have hP := factPlaces D.R.toFrame
  constructor
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have h1 : plGG D (b, t) = plGG D (b', t') := congrArg Subtype.val (D.eTau.symm.injective h)
    cases b <;> cases b' <;> simp only [plGG, if_true, if_false, Bool.false_eq_true] at h1
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
    · exact absurd h1 (hP.2 _ _)
    · exact absurd h1.symm (hP.2 _ _)
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
  · intro τ
    rcases (hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨(false, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])
    · refine ⟨(true, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])

def plEquiv (D : D7) : (Bool × HH D) ≃ D.what₂.Tau := Equiv.ofBijective _ (tauPl_bijective D)

theorem plEquiv_apply (D : D7) (z : Bool × HH D) : plEquiv D z = tauPl D z := rfl

theorem inertK_iff (D : D7) (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l) : GL3Theta.InertK D l ↔ (IsResidueClassZero D l ∨ IsSg D l) := by
  have hq : jacobiSym (-(D.host.d : ℤ)) D.host.q = 1 := by
    have := D.host.hyp
    unfold Formalism.FrobeniusOrbits.HostHyp at this
    tauto
  have hd := D.host.hyp.2.1
  unfold GL3Theta.InertK IsResidueClassZero IsSg Host.cls primeClass
  have h2 : l ≠ 2 := by omega
  by_cases hs : l ∈ D.host.small
  · rw [if_pos hs, D.host.QS_split l hl h2 (Nat.dvd_of_mem_primeFactors hs)]; simp
  rw [if_neg hs]
  by_cases h1 : l = D.host.q
  · rw [if_pos h1, h1, hq]; simp
  rw [if_neg h1]
  by_cases h3 : l = D.host.d
  · rw [if_pos h3, h3]
    have : jacobiSym (-(D.host.d : ℤ)) D.host.d = 0 := by
      haveI : NeZero D.host.d := ⟨hd.ne_zero⟩
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.neg_gcd, Int.gcd_self]
      simpa using hd.ne_one
    rw [this]; simp
  rw [if_neg h3]
  have cop : Int.gcd (-(D.host.d : ℤ)) (l : ℤ) = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hd hl).mpr (Ne.symm h3)
  rcases jacobiSym.eq_one_or_neg_one cop with h | h
  · rw [if_pos h, h]; simp
  · rw [if_neg (by rw [h]; decide)]
    split_ifs <;> simp [h]

theorem case_iff (D : D7) (l : ℕ) (hl : l.Prime) : IndefiniteRowSideFullHecke.ShapeDegreeParity.CaseA D l ↔ IndefiniteRowSideFullHecke.TeichmullerFactorisation.InertNotConj D l := by
  unfold IndefiniteRowSideFullHecke.ShapeDegreeParity.CaseA IndefiniteRowSideFullHecke.TeichmullerFactorisation.InertNotConj
  exact and_congr_right fun h5 => and_congr_left' (inertK_iff D l hl h5)

theorem even_nP (D : D7) (l : ℕ) (h : IndefiniteRowSideFullHecke.TeichmullerFactorisation.InertNotConj D l) : Even (nP D l) := by
  unfold nP
  split_ifs with hs
  · exact even_two_mul _
  · exact h.2.2 (h.2.1.resolve_right hs)

end GlobalTheory.InertCompare

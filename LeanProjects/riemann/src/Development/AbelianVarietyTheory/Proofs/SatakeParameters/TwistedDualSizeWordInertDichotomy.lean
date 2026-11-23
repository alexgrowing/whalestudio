import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordInertPrimeDichotomyStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem alternates_parity {n : ℕ} [NeZero n] {up : ZMod n → Bool} (h : Alternates up) :
    ∃ d : ℕ, ∀ a : ZMod n, up a = decide ((a.val + d) % 2 = 1) := by
  refine ⟨if up 0 then 1 else 0, fun a => ?_⟩
  have key : ∀ k : ℕ, up (k : ZMod n) = decide ((k + (if up 0 then 1 else 0)) % 2 = 1) := by
    intro k
    induction k with
    | zero => cases h0 : up 0 <;> simp [h0]
    | succ k ih =>
      have e : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by push_cast; rfl
      rw [e, h, ih]
      generalize (if up 0 = true then 1 else 0) = d
      by_cases hk : (k + d) % 2 = 1
      · have : ¬ (k + 1 + d) % 2 = 1 := by omega
        simp [hk, this]
      · have : (k + 1 + d) % 2 = 1 := by omega
        simp [hk, this]
  simpa using key a.val

theorem recWord_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 11 ≤ l → ψ.1.2 = -1 →
    WordsNT (recWord L j ε g) ∨ ∃ d, WordsAT l (recWord L j ε g) d := by
  intro D L C j ε n g ψ l hR hO hl hψ
  obtain ⟨rfl, hg⟩ := hO
  obtain ⟨τ, rfl⟩ : ∃ τ, g = letter τ ψ := ⟨g 0, funext hg⟩
  clear hg
  have hT := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR
  obtain ⟨hBox, hcase⟩ := GlobalTheory.T.twistedDualPageWord_inert_prime_dichotomy L C j ε τ ψ l hR hl hψ
  have hsz : ∀ a, (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a :=
    fun a => (hT a).1
  have hη : ∀ a, etaHat L < (recWord L j ε (letter τ ψ)).sz a := fun a => by
    have h6 : ((etaHat L : ℕ) : ℤ) < (pageWord L j ε τ ψ).sz a := hBox.2.2.2.2.2 a
    rw [← hsz a] at h6
    exact_mod_cast h6
  have hSmall : Small (recWord L j ε (letter τ ψ)) :=
    ⟨hBox.1, hBox.2.1, hBox.2.2.1, hBox.2.2.2.1, hBox.2.2.2.2.1, hη⟩
  rcases hcase with ⟨halt, ⟨a, ha⟩, hthree⟩ | ⟨-, ⟨hev, halt, hbig⟩, -⟩
  · left
    refine ⟨hSmall, halt, ⟨a, fun h => ha ((hT a).2.2.2.1 h)⟩, fun i h => hthree i ?_⟩
    exact ⟨(hT _).2.2.2.1 h.1, (hT _).2.2.2.1 h.2.1, (hT _).2.2.2.1 h.2.2⟩
  · right
    haveI : NeZero (orderOf ψ) := ⟨(orderOf_pos ψ).ne'⟩
    obtain ⟨d, hd⟩ := alternates_parity (up := (recWord L j ε (letter τ ψ)).up) halt
    refine ⟨d, hev, hd, hSmall, fun a => ?_, fun M hM a => ?_⟩
    · have hmax : max (etaHat L) ((recWord L j ε (letter τ ψ)).sz a + sHat L) =
          (recWord L j ε (letter τ ψ)).sz a + sHat L := max_eq_right (by have := hη a; omega)
      change (if (!pos ε (letter τ ψ a)) = true then etaHat L else
          max (etaHat L) ((recWord L j ε (letter τ ψ)).sz a + sHat L)) = _ ∧
        (if (!pos ε (letter τ ψ a)) = true then
          max (etaHat L) ((recWord L j ε (letter τ ψ)).sz a + sHat L) else etaHat L) = _
      rw [hmax]
      exact ⟨rfl, rfl⟩
    · have hM' : IsGreatest (Set.range (pageWord L j ε τ ψ).sz) (M : ℤ) := by
        obtain ⟨⟨b, hb⟩, hub⟩ := hM
        refine ⟨⟨b, by rw [← hsz b, hb]⟩, ?_⟩
        rintro _ ⟨c, rfl⟩
        rw [← hsz c]
        exact_mod_cast hub ⟨c, rfl⟩
      obtain ⟨-, h2, h3⟩ := hbig M hM' a
      rw [← hsz a] at h2 h3
      push_cast at h2 h3
      exact ⟨h2, h3⟩

end GlobalTheory.HTW.Rec

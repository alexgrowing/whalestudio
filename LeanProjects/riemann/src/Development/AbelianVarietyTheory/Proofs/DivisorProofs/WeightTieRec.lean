import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare

theorem mem_tops_rec (D : D7) (z : Bool × Formalism.MainNotions.G.HH D) :
    tauPl D z ∈ topsOf D.host D.eTau ↔ z.1 = false ∧ z.2 ∈ D.host.TT := by
  classical
  have hinj := D.R.toFrame.tau1_injective
  have hP := factPlaces D.R.toFrame
  have h0 : (D.eTau (tauPl D z) : D.R.GG) = Formalism.MainNotions.G.plGG D z := by simp [tauPl]
  unfold topsOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h0]
  unfold Host.topPlaces
  rw [Finset.mem_image]
  obtain ⟨b, t⟩ := z
  constructor
  · rintro ⟨t', ht, h⟩
    cases b <;> simp only [Formalism.MainNotions.G.plGG, if_true, if_false, Bool.false_eq_true] at h
    · exact ⟨rfl, (hinj h) ▸ ht⟩
    · exact absurd h (hP.2 _ _)
  · rintro ⟨h1, h2⟩
    refine ⟨t, h2, ?_⟩
    simp only at h1
    simp [Formalism.MainNotions.G.plGG, h1]

theorem weightTie_rec : ∀ (D : D7) (large₂ : SizeData₂ D) (EX : ErrX D), (∃ n : ℕ, D.s.Del = n) → ∀ (u : D.what₂.Word),
    PlaceLogThetaBounds.WeightTie (numDatumOfParameters D large₂) (Pr := recPrimes EX) (recWts EX) (plRec D) u (codeRec large₂ u) := by
  rintro D large₂ EX ⟨n, hn⟩ u
  have hfl : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del := by rw [hn, Nat.floor_natCast]
  refine ⟨⟨fun τ => ⟨D.hc τ, rfl⟩, BadPrimesPeriodBound.recWts_row EX, ?_, ?_⟩, fun z => mem_tops_rec D z,
    fun z => ⟨BadPrimesPeriodBound.recWts_row EX u _, fun i => ?_⟩⟩
  · intro a b τ h
    exact (D.hcW_first a τ h).trans (D.hcW_first b τ h).symm
  · intro a b τ h
    have h' : D.R.k - 1 < D.R.k := h
    have h0 : 0 < D.R.k := by omega
    exact (D.hcW_last a τ h0).trans (D.hcW_last b τ h0).symm
  · show (D.hcW u (tauPl D z)).u i = _
    unfold NumDatum.uW
    obtain ⟨i, hi⟩ := i
    have hi' : i < D.R.k := hi
    by_cases h : 1 ≤ i ∧ i + 1 < D.R.k
    · rw [dif_pos h]
      obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
      have hl : l < D.R.k - 2 := by omega
      have a := D.s.u_letter u (tauPl D z) l hl
      rw [D.hcW_v, ← hfl] at a
      exact a
    · rw [dif_neg h]
      by_cases h0 : i = 0
      · subst h0
        exact D.hcW_first u _ hi'
      · have h1 : i = D.R.k - 1 := by omega
        subst h1
        exact D.hcW_last u _ (by omega)

end GlobalTheory.ColumnNormCompare

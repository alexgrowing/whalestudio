import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizeBoundWindow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeAndBoundStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_thick_iff : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → ∀ i, (pageWord L j ε τ φ).thick i ↔ Thick D.host (letter τ φ i) := by
  intro D L C j ε τ φ hR i
  obtain ⟨hlo, -⟩ := bHat_window L C hR
  obtain ⟨hwM, hwle⟩ := GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR
  have hR' := hR
  obtain ⟨hC, hw, ht, hwb, -, hb⟩ := hR'
  obtain ⟨c, hc⟩ := D.R.t_odd
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by nlinarith
  have hdiv : (D.R.t + 1) / 2 = c + 1 := by omega
  have hdivZ : ((D.R.t : ℤ) + 1) / 2 = (c : ℤ) + 1 := by omega
  have htc : (D.R.t : ℝ) = 2 * c + 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ L.sc.b by linarith)
  have hle := Nat.le_ceil L.sc.b
  have hsub : c + 1 ≤ ⌈L.sc.b⌉₊ := by
    have : ((c + 1 : ℕ) : ℝ) ≤ (⌈L.sc.b⌉₊ : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hbH : bHat L + (c + 1) = ⌈L.sc.b⌉₊ := by
    unfold bHat
    rw [hdiv]
    omega
  have hfl := Nat.lt_floor_add_one L.etaSz
  have hη : etaHat L = ⌊L.etaSz⌋₊ + D.R.t + 2 := rfl
  have hsz : ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ + ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = true) ∨
      ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ - ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = false) := by
    show szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _ ∨
      szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _
    unfold szT
    cases pos ε (letter τ φ i) <;> simp [hdivZ]
  have hbW : (pageWord L j ε τ φ).b = bHat L := rfl
  have hηW : (pageWord L j ε τ φ).η = etaHat L := rfl
  unfold WordData.thick
  rw [hbW, hηW, hη]
  generalize hE : ⌊(hcAt D (letter τ φ i)).e j⌋ = E at hsz
  constructor
  · rintro ⟨ha, hz⟩
    by_contra hnT
    have hEw : E ≤ (wMax D : ℤ) := hE ▸ hwle _ j hnT
    have hlt2 : ((wMax D + (c + 1) : ℕ) : ℝ) < (bHat L : ℝ) := by
      push_cast
      rw [htc] at hlo ht
      linarith
    have hlt3 : wMax D + (c + 1) < bHat L := by exact_mod_cast hlt2
    omega
  · intro hT
    obtain ⟨hA, hB⟩ := GlobalTheory.T.floor_size_bounds_at_thick_embedding L _ j hT
    rw [hE] at hA hB
    have hBE : ((⌈L.sc.b⌉₊ : ℤ)) ≤ E := by
      have : ((⌈L.sc.b⌉₊ : ℤ) : ℝ) < ((E + 1 : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_lt.mp this
      omega
    have hEB : E < (⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 := by
      have : ((E : ℤ) : ℝ) < (((⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp this
    omega

end GlobalTheory.HTW

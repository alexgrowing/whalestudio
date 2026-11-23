import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem haarUp (hSF : HaarUniqueSF) {k r : ℕ} {U : Set (Mat k r)} {μ₀ μ : Measure (Mt k r)}
    (hU : IsClosedSubgroup U) (h₀ : Formalism.FourierDecayAlt.B.IsHaarOn U μ₀) (hμ : Formalism.MainNotions.S.IsHaarOn U μ) :
    Formalism.FourierDecayAlt.B.IsHaarOn U μ := by
  obtain ⟨c, hc0, rfl⟩ := hSF k r U μ₀ μ hU h₀ hμ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.smul_apply, h₀.conc, smul_zero]
  · intro a ha
    rw [Measure.map_smul, h₀.left a ha]
  · intro a ha
    rw [Measure.map_smul, h₀.right a ha]
  · intro K hK
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h₀.finite_compact K hK)
  · exact smul_ne_zero hc0 h₀.ne_zero

theorem isHaarOn_fourier_of_isHaarOn_main (hSF : HaarUniqueSF) (hCW : ClosedW) (hHW : HaarWExists) {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hμ : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW := by
  obtain ⟨μ₀, h₀⟩ := hHW k r z hz hT
  exact haarUp hSF (hCW k r z) h₀ hμ

theorem haarUp_N (hSF : HaarUniqueSF) (hCN : ClosedN) (hHN : HaarNExists) {k r : ℕ}
    {μN : Measure (Mt k r)} (hμ : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN := by
  obtain ⟨μ₀, h₀⟩ := hHN k r
  exact haarUp hSF (hCN k r) h₀ hμ

theorem haarUp_G (hSF : HaarUniqueSF) (hCG : ClosedG) (hHG : HaarGExists) {k r : ℕ}
    {μG : Measure (Mt k r)} (hμ : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG) : Formalism.FourierDecayAlt.B.IsHaarOn (GV k r) μG := by
  obtain ⟨μ₀, h₀⟩ := hHG k r
  exact haarUp hSF (hCG k r) h₀ hμ

theorem haar_measure_univ_lt_infinity_of_compactW (hCpW : CompactW) {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hμ : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW) : μW Set.univ < ∞ := by
  have hK : μW (UWset k r z : Set (Mt k r)) < ∞ := hμ.finite_compact _ (hCpW k r z hz hT)
  have hc : μW (UWset k r z : Set (Mt k r))ᶜ = 0 := hμ.conc
  refine lt_of_le_of_lt (measure_univ_le_add_compl (μ := μW) (UWset k r z : Set (Mt k r))) ?_
  exact ENNReal.add_lt_top.2 ⟨hK, hc ▸ ENNReal.zero_lt_top⟩

theorem conjInv_N (hSF : HaarUniqueSF) (hCN : ClosedN) (hHN : HaarNExists) (hc : ConjInvRaw) {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {μN : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hμ : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN :=
  hc k r z μN hz hT (haarUp_N hSF hCN hHN hμ)

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

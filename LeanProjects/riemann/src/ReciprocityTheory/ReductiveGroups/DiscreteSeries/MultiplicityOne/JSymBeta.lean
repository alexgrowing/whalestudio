import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UuInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSymBetaA

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stSymBeta (h : UnitaryGroupStructuralFacts) : StSymBeta := by
  have hSym := stSym h
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, hGL, -, -, -, hCl, -⟩, -⟩ := h
  unfold StSymBeta
  intro k r Wp _ _ _ D X hD hX γ hγ A hA hJ f F' hf hF'
  have hfi := SymBetaA.integrable_of_inCC hGI hGL hCl D hA hf
  have hae := (hJ (scalF Wp f) (SymBetaA.inCC_five_four' (SymBetaA.inCC_scalF hf))).1
  have hbd : volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = Tz k r D.z * Tz k r D.z} = 0 :=
    SymBetaA.volume_normSq_eq _
  unfold beta betaBig
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict hae, measure_eq_zero_iff_ae_notMem.1 hbd] with q hq hq2
  by_cases hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0
  · simp [hw]
  have hQ : q ∈ Qset D := lt_of_le_of_ne (SymBetaA.bcWeight_nonneg _ _ q) (Ne.symm hw)
  have hle : Tz k r D.z * Tz k r D.z ≤ Complex.normSq q.2 := by
    by_contra hc
    apply hw
    rw [bcWeight, hD.z_eq, if_neg hc]
  have hlt : Tz k r D.z * Tz k r D.z < Complex.normSq q.2 :=
    lt_of_le_of_ne hle (fun e => hq2 e.symm)
  have hEf : Ef D (scalF Wp f) q ≠ ⊤ := (hq hQ).2.ne
  have e : JF D (scalF Wp (f ∘ th k r γ)) (bigCell k r q.1 (D.μsec q.2)) =
      JF D (scalF Wp f) (bigCell k r q.1 (D.μsec q.2)) :=
    hSym k r Wp D X hD hX γ hγ f q hfi hQ hlt hEf
  simp only [e]

end ReciprocityTheory.ChartRestriction.DS.Mult1

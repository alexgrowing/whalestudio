import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ExistsKhwGenSubOfKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeHW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_lowK_eq (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) S) : S = V.map D.subtype := by
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S := by
    intro k hk x hx
    exact hST.2.1 k (by rw [mir_Kset_eq]; exact hk) x hx
  have hSM : S ≤ (genSub E V).map D.subtype := data_kfin_le hgap hσ hD hV hc hVK S hS hST.1 hSK'
  have hSD : S ≤ D := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 (hSM hx)
    exact y.2
  obtain ⟨w, hwS, hw0, hwhw⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
  have hwG : w ∈ genSub E V := by
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSM hwS)
    have : y = w := Subtype.ext hyw
    exact this ▸ hy
  have hwV : w ∈ V :=
    khw_lowK_mem hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap hwG hwhw
  have hTK : Formalism.MainNotions.S.IsKStableOn ε σ (V.map D.subtype) := by
    intro g hg x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
    rw [mir_Kset_eq] at hg
    obtain ⟨u, hu, huv⟩ := hVK g hg v hv
    exact Submodule.mem_map.2 ⟨u, hu, by simpa using huv⟩
  have hwT : (w : H) ∈ V.map D.subtype := Submodule.mem_map_of_mem hwV
  have hle : S ≤ V.map D.subtype := by
    rcases hST.2.2.1 (S ⊓ V.map D.subtype) inf_le_left
        (fun g hg x hx => Submodule.mem_inf.2
          ⟨hST.2.1 g hg x (Submodule.mem_inf.1 hx).1, hTK g hg x (Submodule.mem_inf.1 hx).2⟩) with h | h
    · exfalso
      apply hw0
      have hm : (w : H) ∈ S ⊓ V.map D.subtype := Submodule.mem_inf.2 ⟨hwS, hwT⟩
      rw [h] at hm
      exact (Submodule.coe_eq_zero).1 ((Submodule.mem_bot ℂ).1 hm)
    · rw [← h]
      exact inf_le_right
  rcases (data_isKTypeOf hgap hσ hD hV hc hVK).2.2.1 S hle hST.2.1 with h | h
  · exfalso
    apply hw0
    have hm : (w : H) ∈ S := hwS
    rw [h] at hm
    exact (Submodule.coe_eq_zero).1 ((Submodule.mem_bot ℂ).1 hm)
  · exact h

end ReciprocityTheory.ChartRestriction.DS

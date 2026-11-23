import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataClosGenEqTop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.MultOne

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_lowK_eq (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) S) : S = V.map D.subtype := by
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  have hSf : FiniteDimensional ℂ S := hST.1
  have hSK : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S := hST.2.1
  have hSgen : S ≤ (genSub E V).map D.subtype :=
    ReciprocityTheory.ChartRestriction.DS.G2.data_kfin_le ⟨hmono, h, hh, hbig⟩ hσ hD hV hc hVK S hS hSf hSK
  have hSD : S ≤ D := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hSgen hx
    exact y.2
  obtain ⟨w, hwS, hw0, hwK⟩ := ReciprocityTheory.ChartRestriction.DS.exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
  have hwG : w ∈ genSub E V := by
    obtain ⟨y, hy, hyw⟩ := hSgen hwS
    have : y = w := Subtype.ext hyw
    exact this ▸ hy
  obtain ⟨w₀, hw₀V, -, m, ws, hwsum, hws⟩ :=
    ReciprocityTheory.ChartRestriction.DS.G2.k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hwG hwK
  have hz : ∀ j, ws j = 0 := by
    intro j
    by_contra hne
    obtain ⟨-, hpos, hle⟩ := (hws j).2 hne
    have : (0:ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hwV : w ∈ V := by
    rw [hwsum, Finset.sum_eq_zero (fun j _ => hz j), add_zero]
    exact hw₀V
  have hVT := ReciprocityTheory.ChartRestriction.DS.G2.data_isKTypeOf ⟨hmono, h, hh, hbig⟩ hσ hD hV hc hVK
  have hwVm : (w : H) ∈ V.map D.subtype := ⟨w, hwV, rfl⟩
  have hwne : (w : H) ≠ 0 := fun h0 => hw0 (Submodule.coe_eq_zero.1 h0)
  have hinf : S ⊓ V.map D.subtype = S := by
    rcases hST.2.2.1 (S ⊓ V.map D.subtype) inf_le_left
      (fun g hg v hv => ⟨hST.2.1 g hg v hv.1, hVT.2.1 g hg v hv.2⟩) with h0 | h1
    · exfalso
      apply hwne
      have hm : (w : H) ∈ S ⊓ V.map D.subtype := ⟨hwS, hwVm⟩
      rw [h0] at hm
      exact (Submodule.mem_bot ℂ).1 hm
    · exact h1
  have hSV : S ≤ V.map D.subtype := by
    rw [← hinf]
    exact inf_le_right
  rcases hVT.2.2.1 S hSV hST.2.1 with h0 | h1
  · exfalso
    apply hwne
    rw [h0] at hwS
    exact (Submodule.mem_bot ℂ).1 hwS
  · exact h1

end ReciprocityTheory.ChartRestriction.DS.G2

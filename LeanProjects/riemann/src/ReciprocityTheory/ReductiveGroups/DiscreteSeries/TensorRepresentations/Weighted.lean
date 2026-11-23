import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamLeOfKTypes
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedB

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem weighted_datum {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hgap : StdGap ε lam)
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε =>
        ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε)))
        2 (Formalism.REAL.muG ε) := by
  intro v hv w hw
  show MemLp (wdF ε (wdCoef ε ((w : smD ε (rreg ε)) : L2 ε) v)) 2 (Formalism.REAL.muG ε)
  rcases isEmpty_or_nonempty (Fin n) with hn | hne
  · have e : wdF ε (wdCoef ε ((w : smD ε (rreg ε)) : L2 ε) v) = 0 := by
      funext g
      simp [wdF, S7.hs]
    rw [e]
    exact MemLp.zero
  · obtain ⟨i⟩ := hne
    exact wd_key hP hv₀ i (w : L2 ε) (fun x hx => wd_gen_datum hgap hP hv₀ hΨw i w hw x hx) v hv

end ReciprocityTheory.ChartRestriction.DS

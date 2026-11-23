import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def antiE (E : Fin n → Fin n → Module.End ℂ M) : Fin n → Fin n → Module.End ℂ M :=
  fun a b => -E (Fin.rev b) (Fin.rev a)

theorem antiE_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (antiE E) := by
  intro a b c d
  have h := hE (Fin.rev d) (Fin.rev c) (Fin.rev b) (Fin.rev a)
  simp only [Fin.rev_inj, show (c = b) ↔ (b = c) from eq_comm,
    show (a = d) ↔ (d = a) from eq_comm] at h
  simp only [antiE, neg_mul_neg]
  rw [← neg_sub, h]
  split_ifs <;> simp <;> abel

theorem antiE_hw {E : Fin n → Fin n → Module.End ℂ M} {ν : Fin n → ℝ} {v : M} (hv : IsHWVec E ν v) :
    IsHWVec (antiE E) (fun r => -ν (Fin.rev r)) v := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp [antiE, hv.1 (Fin.rev a)]
  · simp [antiE, hv.2 (Fin.rev b) (Fin.rev a) (Fin.rev_lt_rev.mpr hab)]

end ReciprocityTheory.ChartRestriction.DS

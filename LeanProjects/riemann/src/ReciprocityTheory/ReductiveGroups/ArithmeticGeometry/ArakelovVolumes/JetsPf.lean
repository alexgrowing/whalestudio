import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement

namespace ReciprocityTheory.ChartRestriction.G.AR

theorem mem_multiLt_iff {D a : ℕ} {α : Fin D → ℕ} : α ∈ multiLt D a ↔ ∑ k, α k < a := by
  simp [multiLt, Finset.mem_biUnion, Finset.Nat.mem_antidiagonalTuple]

end ReciprocityTheory.ChartRestriction.G.AR

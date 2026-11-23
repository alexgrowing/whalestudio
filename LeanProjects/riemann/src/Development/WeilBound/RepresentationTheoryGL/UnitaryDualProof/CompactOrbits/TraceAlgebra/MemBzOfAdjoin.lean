import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.NilpotentTraces.TrNil
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.CoefficientTraces.TraceAllHolds
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.LinearConjugation.ToLinAlgEquivEq
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.RestrictionHomomorphisms.ResHomApply

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Alg

open PositivityTheory.RgUd.T

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

theorem mem_Bz_of_adjoin' {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x s : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Bz Z) (hs : s ∈ Algebra.adjoin k {x}) : s ∈ Bz Z := by
  intro a ha
  exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hs (hx a ha)).eq

theorem dich : Dich (k := k) := by
  classical
  intro n Z hZ y
  by_cases hne : ∃ x₀ ∈ Bz Z, pZ Z x₀ = y
  · obtain ⟨x₀, hx₀, hy₀⟩ := hne
    obtain ⟨s₀, hs₀, hss₀, hn₀⟩ := Jcnil.jc k n x₀
    have hs₀B : s₀ ∈ Bz Z := mem_Bz_of_adjoin' k hx₀ hs₀

    have key : ∀ x ∈ Bz Z, pZ Z x = y → ∃ g ∈ Gz Z, ∃ s, s ∈ Algebra.adjoin k {x} ∧ IsNilpotent (x - s) ∧
        g.val * s * g⁻¹.val = s₀ := by
      intro x hx hy
      obtain ⟨s, hs, hss, hn⟩ := Jcnil.jc k n x
      have hsB : s ∈ Bz Z := mem_Bz_of_adjoin' k hx hs
      have htr : ∀ z ∈ Z, ∀ j : ℕ, trace (z * s ^ j) = trace (z * s₀ ^ j) := by
        intro z hz j
        rw [← Jcnil.trNil k n x s z hs hn (hx z hz) j, ← Jcnil.trNil k n x₀ s₀ z hs₀ hn₀ (hx₀ z hz) j]
        exact Trall.trace_all_holds k n Z x x₀ (hy.trans hy₀.symm) z hz j
      obtain ⟨g, hg, hgs⟩ := Conj2.conj_of Iso2.isoOfTrace n Z hZ s s₀ hsB hs₀B hss hss₀ htr
      exact ⟨g, hg, s, hs, hn, hgs⟩
    by_cases hZs : s₀ ∈ Z
    · refine Or.inl ⟨s₀, hZs, fun x hx hy => ?_⟩
      obtain ⟨g, hg, s, hs, hn, hgs⟩ := key x hx hy
      have hgc : g.val * s₀ = s₀ * g.val := (hg s₀ hZs).symm
      have : s = s₀ := by
        have h1 : g.val * s = s₀ * g.val := by
          rw [← hgs, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.mul_one]
        have h2 : g.val * s = g.val * s₀ := h1.trans hgc.symm
        have := congrArg (fun m => g⁻¹.val * m) h2
        simpa [← Matrix.mul_assoc, ← Units.val_mul] using this
      rw [← this]
      exact hn
    · refine Or.inr ⟨s₀, hs₀B, hZs, hss₀, fun x hx hy => ?_⟩
      obtain ⟨g, hg, s, hs, hn, hgs⟩ := key x hx hy
      refine ⟨g, hg, ?_, ?_⟩
      · have e : g.val * x * g⁻¹.val - s₀ = g.val * (x - s) * g⁻¹.val := by
          rw [← hgs, Matrix.mul_sub, Matrix.sub_mul]
        rw [e]
        obtain ⟨m, hm⟩ := hn
        refine ⟨m, ?_⟩
        have hconj : ∀ j : ℕ, (g.val * (x - s) * g⁻¹.val) ^ j = g.val * (x - s) ^ j * g⁻¹.val := by
          intro j
          induction j with
          | zero => simp [← Units.val_mul]
          | succ j ih =>
            rw [pow_succ, ih, pow_succ]
            simp only [Matrix.mul_assoc]
            congr 2
            rw [← Matrix.mul_assoc g⁻¹.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [hconj, hm]
        simp
      · have hcs : Commute x s := (Algebra.commute_of_mem_adjoin_singleton_of_commute hs (Commute.refl x)).symm.symm
        rw [← hgs]
        have e1 : g.val * x * g⁻¹.val * (g.val * s * g⁻¹.val) = g.val * (x * s) * g⁻¹.val := by
          simp only [Matrix.mul_assoc]
          congr 2
          rw [← Matrix.mul_assoc g⁻¹.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        have e2 : g.val * s * g⁻¹.val * (g.val * x * g⁻¹.val) = g.val * (s * x) * g⁻¹.val := by
          simp only [Matrix.mul_assoc]
          congr 2
          rw [← Matrix.mul_assoc g⁻¹.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        show _ * _ = _ * _
        rw [e1, e2, hcs.eq]
  · refine Or.inl ⟨0, Z.zero_mem, fun x hx hy => absurd ⟨x, hx, hy⟩ hne⟩

end PositivityTheory.RgUd.T.Alg

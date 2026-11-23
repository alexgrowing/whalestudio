import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaOperatorBasis

noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility

theorem muStd_exists (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) : ∃ μ, PI.MuStd ν μ := by
  have hfg : (weyl ℤ N N le_rfl ν).FG :=
    (Formalism.L2.DIV.we_nabla_fg N N ν).of_le (weylLeDual ℤ N N le_rfl ν hν)
  have : Module.Finite ℤ (weyl ℤ N N le_rfl ν) := Module.Finite.iff_fg.mpr hfg
  let e := (Module.Free.chooseBasis ℤ (weyl ℤ N N le_rfl ν)).reindex (Fintype.equivFin _)
  have hmem : hw ℤ le_rfl ν ∈ weyl ℤ N N le_rfl ν := Submodule.subset_span ⟨[], rfl⟩
  have hne : (⟨hw ℤ le_rfl ν, hmem⟩ : weyl ℤ N N le_rfl ν) ≠ 0 := fun h0 =>
    hwNe ℤ N N le_rfl ν (congrArg Subtype.val h0)
  have : Nontrivial (weyl ℤ N N le_rfl ν) := nontrivial_of_ne _ _ hne
  exact ⟨_, _, e, Fin.pos_iff_nonempty.mpr e.index_nonempty, rfl⟩

end PI.SlopeSteps

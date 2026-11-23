import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.KappaZeroD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OrbEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SemiSemi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ExistsRho

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.finUq : UpperTheory.V.Z.Sym.Loc.FinUq := by
  intro O K _ _ _ _ _ Δ τ L c d m h δ ι P hM
  refine ⟨orbEq O K Δ τ L c d m h δ ι P hM, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := finU O K Δ τ L c d m h δ ι P hM
    refine ⟨s, fun y hy => hs y ?_⟩
    by_contra hn
    exact hy (by simp [UpperTheory.V.Z.Sym.Glob.one, hn])
  · intro y
    refine QuotientGroup.induction_on y ?_
    intro y
    have e : MulAction.stabilizer (U3 Δ) (QuotientGroup.mk y : U3 Δ ⧸ KU O Δ)
        = (KU O Δ).comap (MulAut.conj y⁻¹).toMonoidHom := by
      ext g
      simp [MulAction.mem_stabilizer_iff, QuotientGroup.eq, mul_assoc]
      constructor
      · intro hg
        simpa [mul_assoc] using (KU O Δ).inv_mem hg
      · intro hg
        simpa [mul_assoc] using (KU O Δ).inv_mem hg
    rw [e]
    exact stabU O K Δ τ L c d m h δ ι P hM y

import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ChainA
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ChainB

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem exists_normal [FiniteDimensional E W] (N : W →ₗ[E] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W), IsChain N l B ∧
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧ v = ∑ a, (if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0) ∧
      ∀ A : W →ₗ[E] W, A ∘ₗ N = N ∘ₗ A → ∀ (a : ι) (i : Fin (l a)), (i : ℕ) < s a → B.repr (A v) ⟨a, i⟩ = 0 := by
  obtain ⟨ι, _, l, s, B, hB, hl, hs, hC, hv⟩ := exists_good N hN v
  exact ⟨ι, inferInstance, l, s, B, hB, hl, hs, hv, fun A hA a i hi =>
    repr_centralizer_eq_zero N l B hB s hs hC v hv A hA a i hi⟩

end PositivityTheory.RgUd.T.Nil.Orb.BReps

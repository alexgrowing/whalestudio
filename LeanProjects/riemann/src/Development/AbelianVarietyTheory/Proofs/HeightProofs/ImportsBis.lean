import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups

namespace GlobalTheory.MiscellaneousLemmas

open scoped TensorProduct

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : StarRing E] (V : Formalism.BasicNotions.HSpace E) {k : ℕ} (x : Fin k → Formalism.BasicNotions.HSpace.V V), (∀ w ∈ Formalism.BasicNotions.HSpace.L0 V, ∃ (n : Fin k → ℤ), w = ∑ j : Fin k, n j • x j) → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc V v, ∃ (a : Fin k → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), (∀ (j : Fin k), a j ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) ∧ ∀ (i : Fin (Formalism.BasicNotions.HSpace.rank V)), y i = ∑ j : Fin k, a j ⊗ₜ[F] ((Module.Basis.repr (Formalism.BasicNotions.HSpace.frame V) : Formalism.BasicNotions.HSpace.V V → Fin (Formalism.BasicNotions.HSpace.rank V) →₀ E) (x j) : Fin (Formalism.BasicNotions.HSpace.rank V) → E) i := by
  intro F E _ _ _ _ _ _ V k x hx v y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, w, hw, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hx w hw
    refine ⟨fun j => n j • a, fun j => zsmul_mem ha _, fun i => ?_⟩
    simp only [map_sum, map_zsmul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
      Pi.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  | zero => exact ⟨0, fun j => zero_mem _, fun i => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, h⟩ := hy
    obtain ⟨b, hb, h'⟩ := hz
    exact ⟨a + b, fun j => add_mem (ha j) (hb j), fun i => by
      simp [h i, h' i, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  | neg y _ hy =>
    obtain ⟨a, ha, h⟩ := hy
    exact ⟨-a, fun j => neg_mem (ha j), fun i => by
      simp [h i, TensorProduct.neg_tmul, Finset.sum_neg_distrib]⟩

end GlobalTheory.MiscellaneousLemmas

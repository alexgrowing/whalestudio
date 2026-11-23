import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjA

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def IdemStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E), (∀ a, σ a = star a) →
    ∀ W : Finset (Ideal (𝓞 E)), (∀ p ∈ W, p.IsMaximal) →
      (∀ p ∈ W, ∀ q ∈ W, hcompl (K := E) p = hcompl (K := E) q → p = q) →
    ∃ e : Option W → AF F ⊗[F] E,
      (∀ i, e i * e i = e i) ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ (∑ i, e i = 1) ∧
      (∀ i, sigR (AF F) σ (e i) = e i) ∧
      (∀ i, finE F E (e i) ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
        [FiniteDimensional E V] (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
        Submodule.IsLattice E L0 → ∀ v : V,
        (∀ p : W, finE F E (e (some p)) • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (b.equivFun v) ∈
            latHat F E (crdOf b L0) ↔ v ∈ loc (K := E) (p : Ideal (𝓞 E)) L0) ∧
        (finE F E (e none) • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (b.equivFun v) ∈ latHat F E (crdOf b L0) ↔
            ∀ q : Ideal (𝓞 E), q.IsMaximal → (∀ p ∈ W, hcompl (K := E) q ≠ hcompl (K := E) p) →
              v ∈ loc (K := E) q L0)

theorem linOf_one_symm_apply {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (v : V) : (linOf b (1 : GL (Fin M) E)).symm v = v := by
  rw [LinearEquiv.symm_apply_eq, linOf_one_apply]

end PI.UnitaryGroupMassFormula.UJClassMass

end

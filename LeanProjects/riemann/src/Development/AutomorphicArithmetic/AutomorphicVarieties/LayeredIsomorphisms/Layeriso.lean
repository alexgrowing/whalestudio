import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem nonempty_ringEquiv_of_isCyclotomic_finrank_eq (l j k k' : ℕ) (hl : l.Prime) (hk : k ≤ k') (L₀ L₀' L₁ L₁' : Type)
    [Field L₀] [Field L₀'] [Field L₁] [Field L₁'] [Algebra L₀ L₁] [Algebra L₀' L₁']
    (e : L₀ ≃+* L₀') (h₁ : IsCyclotomicExtension {l ^ k} L₀ L₁)
    (h₁' : IsCyclotomicExtension {l ^ k'} L₀' L₁')
    (d₁ : Module.finrank L₀ L₁ = l ^ j) (d₁' : Module.finrank L₀' L₁' = l ^ j) :
    Nonempty (L₁ ≃+* L₁') := by
  haveI : NeZero (l ^ k') := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))) (l ^ k) :=
    (IsCyclotomicExtension.zeta_spec (l ^ k') L₀' L₁').pow (pow_pos hl.pos _)
      (by rw [← pow_add, Nat.sub_add_cancel hk])
  letI : Algebra L₀ L₀' := e.toRingHom.toAlgebra
  letI : Algebra L₀ L₁' := ((algebraMap L₀' L₁').comp e.toRingHom).toAlgebra
  haveI : IsScalarTower L₀ L₀' L₁' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h1 : Module.finrank L₀ L₀' = 1 := by
    rw [← (AlgEquiv.ofRingEquiv (R := L₀) (A₁ := L₀) (A₂ := L₀') (f := e)
      (fun _ => rfl)).toLinearEquiv.finrank_eq, Module.finrank_self]
  have h2 : Module.finrank L₀ L₁' = l ^ j := by
    rw [← Module.finrank_mul_finrank L₀ L₀' L₁', h1, one_mul, d₁']
  haveI : FiniteDimensional L₀ L₁' :=
    Module.finite_of_finrank_pos (by rw [h2]; exact pow_pos hl.pos _)
  haveI : Algebra.IsIntegral L₀ L₁' := Algebra.IsIntegral.of_finite L₀ L₁'
  haveI := hζ.intermediateField_adjoin_isCyclotomicExtension L₀
  let φ := IsCyclotomicExtension.algEquiv {l ^ k} L₀ L₁
    (IntermediateField.adjoin L₀ {IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))})
  have htop : IntermediateField.adjoin L₀
      {IsCyclotomicExtension.zeta (l ^ k') L₀' L₁' ^ (l ^ (k' - k))} = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [IntermediateField.finrank_top', ← φ.toLinearEquiv.finrank_eq, d₁, h2])
  exact ⟨φ.toRingEquiv.trans ((IntermediateField.equivOfEq htop).toRingEquiv.trans
    IntermediateField.topEquiv.toRingEquiv)⟩

theorem UpperTheory.V.Win.layeriso :
    ∀ (l j : ℕ), l.Prime → ∀ (L₀ L₀' L₁ L₁' : Type) [Field L₀] [NumberField L₀] [Field L₀'] [NumberField L₀']
      [Field L₁] [NumberField L₁] [Field L₁'] [NumberField L₁'] [Algebra L₀ L₁] [Algebra L₀' L₁'],
        Nonempty (L₀ ≃+* L₀') → IsLayer l j L₀ L₁ → IsLayer l j L₀' L₁' → Nonempty (L₁ ≃+* L₁') := by
  intro l j hl L₀ L₀' L₁ L₁' _ _ _ _ _ _ _ _ _ _ ⟨e⟩ ⟨⟨k, hk⟩, d⟩ ⟨⟨k', hk'⟩, d'⟩
  rcases le_total k k' with h | h
  · exact nonempty_ringEquiv_of_isCyclotomic_finrank_eq l j k k' hl h L₀ L₀' L₁ L₁' e hk hk' d d'
  · obtain ⟨f⟩ := nonempty_ringEquiv_of_isCyclotomic_finrank_eq l j k' k hl h L₀' L₀ L₁' L₁ e.symm hk' hk d' d
    exact ⟨f.symm⟩

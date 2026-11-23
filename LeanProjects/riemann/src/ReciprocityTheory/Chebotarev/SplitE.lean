import ReciprocityTheory.Chebotarev.SplitA
import ReciprocityTheory.Chebotarev.SplitD
import ReciprocityTheory.Chebotarev.SplitEA

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem splitE_split_ext (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) (hχ : χ ≠ 1) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : Algebra E E') (k : ℕ), 2 ≤ k ∧
      ∀ q : Prm E, ¬ l ∣ Nrm q → χ ((Nrm q : ℕ) : ZMod l) = 1 →
        k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by
  refine ⟨IntermediateField.fixedField (splitEH hirr χ), inferInstance, inferInstance, inferInstance,
    Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)), splitE_two_le hirr χ hχ, ?_⟩
  intro q hl hq
  exact splitE_count hirr χ q hl hq _
    (fun x σ hσ => (IntermediateField.mem_fixedField_iff _ _).1 x.2 σ hσ)

end ReciprocityTheory.Cheb
